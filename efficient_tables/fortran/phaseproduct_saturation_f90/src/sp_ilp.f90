! Kannan SHORTEST + suffix-batch recursion; bounded rational polyhedra only.
! Vertex/greedy-simplex preprocessing is polynomial for the decorated outer family.
module sp_ilp
  use sp_arithmetic, only: ik
  use sp_rational
  use sp_lattice
  implicit none
  type ilp_stats
    integer(ik) :: nodes, vertices, simplex_exchanges, suffix_candidates
    type(lattice_stats) :: lattice
  end type ilp_stats
contains
  subroutine ilp_feasible(a,b,x,status,stats)
    integer(ik), intent(in) :: a(:,:),b(:)
    integer(ik), intent(out) :: x(:)
    integer, intent(out) :: status
    type(ilp_stats), intent(out) :: stats
    integer :: qa(size(a,1),size(a,2)),qb(size(b)),qx(size(x)),i,j,st
    stats%nodes=0_ik; stats%vertices=0_ik; stats%simplex_exchanges=0_ik
    stats%suffix_candidates=0_ik; stats%lattice%lll_swaps=0_ik
    stats%lattice%hkz_calls=0_ik; stats%lattice%svp_candidates=0_ik
    x=0_ik; status=4
    if(size(b)/=size(a,1).or.size(x)/=size(a,2)) return
    call r_start()
    do i=1,size(a,1)
      qb(i)=ri(b(i))
      do j=1,size(a,2)
        qa(i,j)=ri(a(i,j))
      end do
    end do
    call ilp_rational(qa,qb,qx,status,stats)
    if(r_status/=0) status=r_status
    if(status==0) then
      do j=1,size(x)
        x(j)=rtoi(qx(j),st)
        if(st/=0) status=st
      end do
    end if
    if(status/=0) x=0_ik
    call r_finish()
  end subroutine ilp_feasible

  function fits(a,b,x) result(ok)
    integer, intent(in) :: a(:,:),b(:),x(:)
    logical :: ok
    integer :: i
    ok=.false.
    if(r_status/=0) return
    do i=1,size(b)
      if(rc(qdot(a(i,:),x),b(i))>0) return
    end do
    ok=(r_status==0)
  end function fits

  recursive subroutine vertex_subsets(level,start,chosen,a,b,verts,nv,cap,stats)
    integer, intent(in) :: level,start,a(:,:),b(:)
    integer, intent(inout) :: chosen(:),nv,cap
    integer, pointer :: verts(:,:)
    type(ilp_stats), intent(inout) :: stats
    integer :: i,j,n,newcap,st
    integer :: mat(size(chosen),size(chosen)),rhs(size(chosen)),v(size(chosen))
    integer, pointer :: tmp(:,:)
    logical :: ok
    if(r_status/=0) return
    n=size(chosen)
    if(level<=n) then
      do i=start,size(b)-(n-level)
        chosen(level)=i
        call vertex_subsets(level+1,i+1,chosen,a,b,verts,nv,cap,stats)
        if(r_status/=0) return
      end do
      return
    end if
    do i=1,n
      rhs(i)=b(chosen(i)); mat(i,:)=a(chosen(i),:)
    end do
    call qsolve(mat,rhs,v,ok)
    if(.not.ok) return
    if(.not.fits(a,b,v)) return
    ! Duplicates are removed to make the greedy scans substantially smaller.
    do j=1,nv
      ok=.true.
      do i=1,n
        if(rc(v(i),verts(i,j))/=0) ok=.false.
      end do
      if(ok) return
    end do
    if(nv==cap) then
      if(cap>huge(0)/2) then
        r_status=3; return
      end if
      newcap=max(16,2*cap)
      allocate(tmp(n,newcap),stat=st)
      if(st/=0) then
        r_status=3; return
      end if
      if(nv>0) tmp(:,1:nv)=verts(:,1:nv)
      if(associated(verts)) deallocate(verts)
      verts=>tmp; cap=newcap
    end if
    nv=nv+1; verts(:,nv)=v; call tick(stats%vertices)
  end subroutine vertex_subsets

  subroutine simplex_edges(s,b)
    integer, intent(in) :: s(:,:)
    integer, intent(out) :: b(:,:)
    integer :: i,j
    do j=1,size(b,2)
      do i=1,size(b,1)
        b(i,j)=rs(s(i,j+1),s(i,1))
      end do
    end do
  end subroutine simplex_edges

  recursive subroutine ilp_rational(a,b,x,status,stats)
    integer, intent(in) :: a(:,:),b(:)
    integer, intent(out) :: x(:),status
    type(ilp_stats), intent(inout) :: stats
    integer, pointer :: verts(:,:)
    integer :: n,m,nv,cap,i,j,k,rank,rr,freecol,d,den,rhs,gcdv,factor
    integer :: chosen(size(x)),piv(size(x)),s(size(x),size(x)+1)
    integer :: trial(size(x),size(x)+1),edges(size(x),size(x)),inv(size(x),size(x))
    integer :: work(size(x),size(x)),v(size(x),size(x)),eq(size(x)),x0(size(x))
    integer :: center(size(x)),target(size(x)),basis(size(x),size(x)),u(size(x),size(x))
    integer :: star(size(x),size(x)),mu(size(x),size(x)),h(size(x)),coef(size(x))
    integer :: bestdet,newdet,maxi,radius
    logical :: ok,changed
    nullify(verts); nv=0; cap=0; n=size(x); m=size(b)
    status=1; x=r0; call tick(stats%nodes)
    if(r_status/=0) then
      status=r_status; return
    end if
    if(n==0) then
      if(fits(a,b,x)) status=0
      return
    end if
    call vertex_subsets(1,1,chosen,a,b,verts,nv,cap,stats)
    if(r_status/=0.or.nv==0) then
      if(associated(verts)) deallocate(verts)
      if(r_status/=0) status=r_status
      return
    end if
    ! Build a maximal independent list of vertex differences (at most n).
    work=r0; rank=0; s(:,1)=verts(:,1)
    do j=2,nv
      do i=1,n
        edges(:,i)=work(:,i)
      end do
      do i=1,n
        edges(rank+1,i)=rs(verts(i,j),verts(i,1))
      end do
      call qrref(edges,rr,piv)
      if(rr>rank) then
        rank=rr; work=edges; s(:,rank+1)=verts(:,j)
      end if
      if(rank==n) exit
    end do
    if(r_status/=0) then
      status=r_status; deallocate(verts); return
    end if
    if(rank<n) then
      call qrref(work,rank,piv)
      freecol=0
      do j=1,n
        if(.not.any(piv(1:rank)==j)) then
          freecol=j; exit
        end if
      end do
      eq=r0; eq(freecol)=r1
      do i=1,rank
        eq(piv(i))=rn(work(i,freecol))
      end do
      rhs=qdot(eq,verts(:,1)); den=rden(rhs)
      do i=1,n
        den=rm(den,rden(eq(i)))
      end do
      rhs=rm(rhs,den)
      do i=1,n
        eq(i)=rm(eq(i),den)
      end do
      call row_gcd(eq,v,gcdv)
      factor=rd(rhs,gcdv)
      deallocate(verts)
      if(r_status/=0) then
        status=r_status; return
      end if
      if(.not.rzint(factor)) return
      do i=1,n
        x0(i)=rm(v(i,1),factor)
      end do
      call section_solve(a,b,x0,v(:,2:n),x,status,stats)
      return
    end if
    call simplex_edges(s,edges); bestdet=qabs(qdet(edges))
    do
      changed=.false.
      do j=1,nv
        do k=1,n+1
          trial=s; trial(:,k)=verts(:,j)
          call simplex_edges(trial,edges); newdet=qabs(qdet(edges))
          if(rc(newdet,rm(ri(2_ik),bestdet))>0) then
            s=trial; bestdet=newdet; changed=.true.
            call tick(stats%simplex_exchanges)
            exit
          end if
        end do
        if(changed.or.r_status/=0) exit
      end do
      if(.not.changed.or.r_status/=0) exit
    end do
    deallocate(verts)
    if(r_status/=0) then
      status=r_status; return
    end if
    call simplex_edges(s,edges); call qinverse(edges,inv,ok)
    if(.not.ok.or.r_status/=0) then
      status=4
      if(r_status/=0) status=r_status
      return
    end if
    do i=1,n
      center(i)=r0
      do j=1,n+1
        center(i)=ra(center(i),s(i,j))
      end do
      center(i)=rd(center(i),ri(int(n+1,ik)))
    end do
    do i=1,n
      target(i)=qdot(inv(i,:),center)
    end do
    call hkz(inv,basis,u,stats%lattice)
    if(r_status/=0) then
      status=r_status; return
    end if
    call qgs(basis,star,mu,h)
    call babai(basis,star,h,target,coef)
    do i=1,n
      x(i)=qdot(u(i,:),coef)
    end do
    if(fits(a,b,x)) then
      status=0; return
    end if
    maxi=1
    do i=2,n
      if(rc(h(i),h(maxi))>0) maxi=i
    end do
    radius=ri(9_ik*int(n,ik)); coef=r0
    call suffix_search(n,maxi,mu,h,star,target,radius,r0,coef,u,a,b,x,status,stats)
    if(r_status/=0) status=r_status
  end subroutine ilp_rational

  recursive subroutine section_solve(a,b,x0,h,x,status,stats)
    integer, intent(in) :: a(:,:),b(:),x0(:),h(:,:)
    integer, intent(out) :: x(:),status
    type(ilp_stats), intent(inout) :: stats
    integer :: aa(size(a,1),size(h,2)),bb(size(b)),y(size(h,2)),i
    call qmm(a,h,aa)
    do i=1,size(b)
      bb(i)=rs(b(i),qdot(a(i,:),x0))
    end do
    call ilp_rational(aa,bb,y,status,stats)
    if(status/=0) return
    do i=1,size(x)
      x(i)=ra(x0(i),qdot(h(i,:),y))
    end do
    if(.not.fits(a,b,x)) status=4
  end subroutine section_solve

  recursive subroutine suffix_search(j,first,mu,h,star,target,radius,partial,coef,u,a,b,x,status,stats)
    integer, intent(in) :: j,first,mu(:,:),h(:),star(:,:),target(:),radius,partial
    integer, intent(in) :: u(:,:),a(:,:),b(:)
    integer, intent(inout) :: coef(:)
    integer, intent(out) :: x(:),status
    type(ilp_stats), intent(inout) :: stats
    integer :: center,k,q,c,lo,hi,dist,next,x0(size(x)),i
    status=1
    if(r_status/=0) then
      status=r_status; return
    end if
    if(j<first) then
      call tick(stats%suffix_candidates)
      do i=1,size(x)
        x0(i)=qdot(u(i,first:),coef(first:))
      end do
      call section_solve(a,b,x0,u(:,1:first-1),x,status,stats)
      return
    end if
    if(rc(partial,radius)>0) return
    center=rd(qdot(target,star(:,j)),h(j))
    do k=j+1,size(coef)
      center=rs(center,rm(coef(k),mu(k,j)))
    end do
    q=rroot(rd(rs(radius,partial),h(j)))
    lo=rs(rf(center),q); hi=ra(ra(rf(center),q),r1); c=lo
    do while(rc(c,hi)<=0.and.r_status==0)
      dist=rs(c,center); next=ra(partial,rm(h(j),rm(dist,dist)))
      if(rc(next,radius)<=0) then
        coef(j)=c
        call suffix_search(j-1,first,mu,h,star,target,radius,next,coef,u,a,b,x,status,stats)
        if(status/=1) return
      end if
      c=ra(c,r1)
    end do
  end subroutine suffix_search
end module sp_ilp
