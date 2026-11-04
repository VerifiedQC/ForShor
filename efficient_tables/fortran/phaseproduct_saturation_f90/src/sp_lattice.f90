! Exact rational matrix operations and Kannan (1987), Section 2, SHORTEST.
module sp_lattice
  use sp_arithmetic, only: ik
  use sp_rational
  implicit none
  type lattice_stats
    integer(ik) :: lll_swaps, hkz_calls, svp_candidates
  end type lattice_stats
contains
  subroutine tick(x)
    integer(ik), intent(inout) :: x
    if (x<huge(x)) x=x+1_ik
  end subroutine tick

  function qdot(a,b) result(v)
    integer, intent(in) :: a(:),b(:)
    integer :: v,i
    v=r0
    do i=1,size(a)
      v=ra(v,rm(a(i),b(i)))
    end do
  end function qdot

  subroutine qeye(a)
    integer, intent(out) :: a(:,:)
    integer :: i
    a=r0
    do i=1,min(size(a,1),size(a,2))
      a(i,i)=r1
    end do
  end subroutine qeye

  subroutine qmm(a,b,c)
    integer, intent(in) :: a(:,:),b(:,:)
    integer, intent(out) :: c(:,:)
    integer :: i,j,k,v
    do j=1,size(b,2)
      do i=1,size(a,1)
        v=r0
        do k=1,size(a,2)
          v=ra(v,rm(a(i,k),b(k,j)))
        end do
        c(i,j)=v
      end do
    end do
  end subroutine qmm

  subroutine qrref(a,rank,pivots)
    integer, intent(inout) :: a(:,:)
    integer, intent(out) :: rank,pivots(:)
    integer :: i,j,p,k,q,tmp,v
    rank=0
    pivots=0
    do j=1,size(a,2)
      p=0
      do i=rank+1,size(a,1)
        if (.not.rz(a(i,j))) then
          p=i
          exit
        end if
      end do
      if (p==0) cycle
      rank=rank+1
      pivots(rank)=j
      do k=1,size(a,2)
        tmp=a(rank,k); a(rank,k)=a(p,k); a(p,k)=tmp
      end do
      q=a(rank,j)
      do k=1,size(a,2)
        a(rank,k)=rd(a(rank,k),q)
      end do
      do i=1,size(a,1)
        if (i==rank) cycle
        v=a(i,j)
        if (rz(v)) cycle
        do k=1,size(a,2)
          a(i,k)=rs(a(i,k),rm(v,a(rank,k)))
        end do
      end do
      if (rank==size(a,1)) exit
      if (r_status/=0) return
    end do
  end subroutine qrref

  subroutine qsolve(a,b,x,ok)
    integer, intent(in) :: a(:,:),b(:)
    integer, intent(out) :: x(:)
    logical, intent(out) :: ok
    integer :: aug(size(a,1),size(a,2)+1),pv(size(a,1)),rank,n,j
    n=size(a,1); x=r0; ok=.false.
    aug(:,1:n)=a; aug(:,n+1)=b
    call qrref(aug,rank,pv)
    if (rank/=n) return
    do j=1,n
      if(pv(j)/=j) return
    end do
    x=aug(:,n+1); ok=(r_status==0)
  end subroutine qsolve

  subroutine qinverse(a,b,ok)
    integer, intent(in) :: a(:,:)
    integer, intent(out) :: b(:,:)
    logical, intent(out) :: ok
    integer :: aug(size(a,1),2*size(a,1)),pv(size(a,1)),rank,n,j
    n=size(a,1); b=r0; ok=.false.
    aug(:,1:n)=a
    call qeye(aug(:,n+1:2*n))
    call qrref(aug,rank,pv)
    if (rank/=n) return
    do j=1,n
      if (pv(j)/=j) return
    end do
    b=aug(:,n+1:2*n); ok=(r_status==0)
  end subroutine qinverse

  function qdet(a) result(v)
    integer, intent(in) :: a(:,:)
    integer :: v,w(size(a,1),size(a,2)),n,i,j,k,p,tmp,f
    n=size(a,1); w=a; v=r1
    do j=1,n
      p=0
      do i=j,n
        if (.not.rz(w(i,j))) then
          p=i; exit
        end if
      end do
      if (p==0) then
        v=r0; return
      end if
      if (p/=j) then
        v=rn(v)
        do k=1,n
          tmp=w(j,k); w(j,k)=w(p,k); w(p,k)=tmp
        end do
      end if
      v=rm(v,w(j,j))
      do i=j+1,n
        f=rd(w(i,j),w(j,j))
        do k=j+1,n
          w(i,k)=rs(w(i,k),rm(f,w(j,k)))
        end do
        w(i,j)=r0
      end do
    end do
  end function qdet

  function qabs(a) result(v)
    integer, intent(in) :: a
    integer :: v
    v=a
    if (rc(a,r0)<0) v=rn(a)
  end function qabs

  subroutine qgs(g,star,mu,h)
    integer, intent(in) :: g(:,:)
    integer, intent(out) :: star(:,:),mu(:,:),h(:)
    integer :: i,j,k
    mu=r0; star=g; h=r0
    if(r_status/=0) return
    do i=1,size(g,2)
      do j=1,i-1
        if (rz(h(j))) then
          r_status=4; return
        end if
        mu(i,j)=rd(qdot(g(:,i),star(:,j)),h(j))
        if(r_status/=0) return
        do k=1,size(g,1)
          star(k,i)=rs(star(k,i),rm(mu(i,j),star(k,j)))
        end do
      end do
      h(i)=qdot(star(:,i),star(:,i))
      if(r_status/=0) return
      if (rz(h(i))) then
        r_status=4; return
      end if
    end do
  end subroutine qgs

  subroutine qlll(g,u,stats)
    integer, intent(inout) :: g(:,:),u(:,:)
    type(lattice_stats), intent(inout) :: stats
    integer :: star(size(g,1),size(g,2)),mu(size(g,2),size(g,2)),h(size(g,2))
    integer :: i,j,k,c,tmp,half,threefour
    half=rd(r1,ri(2_ik)); threefour=rd(ri(3_ik),ri(4_ik))
    call qgs(g,star,mu,h)
    i=2
    do while(i<=size(g,2).and.r_status==0)
      do j=i-1,1,-1
        c=rf(ra(mu(i,j),half))
        if (rz(c)) cycle
        do k=1,size(g,1)
          g(k,i)=rs(g(k,i),rm(c,g(k,j)))
        end do
        do k=1,size(u,1)
          u(k,i)=rs(u(k,i),rm(c,u(k,j)))
        end do
        call qgs(g,star,mu,h)
      end do
      tmp=rm(rs(threefour,rm(mu(i,i-1),mu(i,i-1))),h(i-1))
      if(rc(h(i),tmp)>=0) then
        i=i+1
      else
        do k=1,size(g,1)
          tmp=g(k,i); g(k,i)=g(k,i-1); g(k,i-1)=tmp
        end do
        do k=1,size(u,1)
          tmp=u(k,i); u(k,i)=u(k,i-1); u(k,i-1)=tmp
        end do
        call tick(stats%lll_swaps)
        call qgs(g,star,mu,h)
        i=max(2,i-1)
      end if
    end do
  end subroutine qlll

  subroutine qbezout(a,b,g,s,t)
    integer, intent(in) :: a,b
    integer, intent(out) :: g,s,t
    integer :: oldr,r,olds,ss,oldt,tt,q,tmp
    oldr=qabs(a); r=qabs(b); olds=r1; ss=r0; oldt=r0; tt=r1
    do while(.not.rz(r).and.r_status==0)
      q=rf(rd(oldr,r))
      tmp=rs(oldr,rm(q,r)); oldr=r; r=tmp
      tmp=rs(olds,rm(q,ss)); olds=ss; ss=tmp
      tmp=rs(oldt,rm(q,tt)); oldt=tt; tt=tmp
    end do
    g=oldr; s=olds; t=oldt
    if(rc(a,r0)<0) s=rn(s)
    if(rc(b,r0)<0) t=rn(t)
  end subroutine qbezout

  subroutine row_gcd(z,v,g)
    integer, intent(in) :: z(:)
    integer, intent(out) :: v(:,:),g
    integer :: w(size(z)),j,k,a,b,s,t,gg,c1,cj
    call qeye(v); w=z
    do j=2,size(z)
      a=w(1); b=w(j)
      if(rz(a).and.rz(b)) cycle
      call qbezout(a,b,gg,s,t)
      do k=1,size(z)
        c1=v(k,1); cj=v(k,j)
        v(k,1)=ra(rm(s,c1),rm(t,cj))
        v(k,j)=ra(rm(rn(rd(b,gg)),c1),rm(rd(a,gg),cj))
      end do
      w(1)=gg; w(j)=r0
    end do
    g=w(1)
    if(rc(g,r0)<0) then
      g=rn(g)
      do k=1,size(z)
        v(k,1)=rn(v(k,1))
      end do
    end if
  end subroutine row_gcd

  recursive subroutine svp_enum(j,mu,h,radius,partial,a,best,bestnorm,stats)
    integer, intent(in) :: j,mu(:,:),h(:),radius,partial
    integer, intent(inout) :: a(:),best(:),bestnorm
    type(lattice_stats), intent(inout) :: stats
    integer :: center,k,q,lo,hi,c,dist,next
    if(r_status/=0) return
    if(j==0) then
      call tick(stats%svp_candidates)
      if(all(a==r0)) return
      ! Handles need not be canonical except zero; check mathematical zero too.
      if(all_zero(a)) return
      if(rc(partial,bestnorm)<0) then
        bestnorm=partial; best=a
      end if
      return
    end if
    if(rc(partial,bestnorm)>0) return
    center=r0
    do k=j+1,size(a)
      center=rs(center,rm(a(k),mu(k,j)))
    end do
    q=rroot(rd(rs(bestnorm,partial),h(j)))
    lo=rs(rf(center),q); hi=ra(ra(rf(center),q),r1); c=lo
    do while(rc(c,hi)<=0.and.r_status==0)
      dist=rs(c,center); next=ra(partial,rm(h(j),rm(dist,dist)))
      if(rc(next,bestnorm)<=0) then
        a(j)=c
        call svp_enum(j-1,mu,h,radius,next,a,best,bestnorm,stats)
      end if
      c=ra(c,r1)
    end do
  end subroutine svp_enum

  function all_zero(a) result(z)
    integer, intent(in) :: a(:)
    logical :: z
    integer :: i
    z=.true.
    do i=1,size(a)
      if(.not.rz(a(i))) z=.false.
    end do
  end function all_zero

  recursive subroutine hkz(f,g,u,stats)
    integer, intent(in) :: f(:,:)
    integer, intent(out) :: g(:,:),u(:,:)
    type(lattice_stats), intent(inout) :: stats
    integer :: t,d,i,j,k,c,tmp,m,bnorm,gcdv
    integer :: star(size(f,1),size(f,2)),mu(size(f,2),size(f,2)),h(size(f,2))
    integer :: a(size(f,2)),best(size(f,2)),v(size(f,2),size(f,2))
    integer :: inv(size(f,2),size(f,2)),qmat(size(f,2),size(f,2))
    integer :: gg(size(f,1),size(f,2)),uu(size(f,2),size(f,2))
    logical :: ok
    call tick(stats%hkz_calls)
    t=size(f,2); d=size(f,1); g=f; call qeye(u)
    if(t<=1) return
    call qlll(g,u,stats)
    do while(r_status==0)
      call reduce_tail(g,u,stats)
      if(rc(rm(ri(4_ik),qdot(g(:,2),g(:,2))),rm(ri(3_ik),qdot(g(:,1),g(:,1))))>=0) exit
      do k=1,d
        tmp=g(k,1); g(k,1)=g(k,2); g(k,2)=tmp
      end do
      do k=1,t
        tmp=u(k,1); u(k,1)=u(k,2); u(k,2)=tmp
      end do
    end do
    if(r_status/=0) return
    call qgs(g,star,mu,h)
    bnorm=qdot(g(:,1),g(:,1)); m=t
    do j=2,t
      if(rc(h(j),bnorm)>=0) then
        m=j-1; exit
      end if
    end do
    a=r0; best=r0; best(1)=r1
    call svp_enum(m,mu(1:m,1:m),h(1:m),bnorm,r0,a(1:m),best(1:m),bnorm,stats)
    if(r_status/=0) return
    call row_gcd(best,v,gcdv)
    if(r_status/=0) return
    if(rc(gcdv,r1)/=0) then
      r_status=4; return
    end if
    call qinverse(v,inv,ok)
    if(r_status/=0) return
    if(.not.ok) then
      r_status=4; return
    end if
    qmat=transpose(inv)
    call qmm(g,qmat,gg); call qmm(u,qmat,uu)
    g=gg; u=uu
    call reduce_tail(g,u,stats)
  end subroutine hkz

  recursive subroutine reduce_tail(g,u,stats)
    integer, intent(inout) :: g(:,:),u(:,:)
    type(lattice_stats), intent(inout) :: stats
    integer :: p(size(g,1),size(g,2)-1),pg(size(g,1),size(g,2)-1)
    integer :: tr(size(g,2)-1,size(g,2)-1),lift(size(g,1),size(g,2)-1)
    integer :: ut(size(u,1),size(g,2)-1),norm,c,i,j
    norm=qdot(g(:,1),g(:,1))
    do j=2,size(g,2)
      c=rd(qdot(g(:,j),g(:,1)),norm)
      do i=1,size(g,1)
        p(i,j-1)=rs(g(i,j),rm(c,g(i,1)))
      end do
    end do
    call hkz(p,pg,tr,stats)
    if(r_status/=0) return
    call qmm(g(:,2:),tr,lift); call qmm(u(:,2:),tr,ut)
    g(:,2:)=lift; u(:,2:)=ut
    do j=2,size(g,2)
      c=rf(ra(rd(qdot(g(:,j),g(:,1)),norm),rd(r1,ri(2_ik))))
      do i=1,size(g,1)
        g(i,j)=rs(g(i,j),rm(c,g(i,1)))
      end do
      do i=1,size(u,1)
        u(i,j)=rs(u(i,j),rm(c,u(i,1)))
      end do
    end do
  end subroutine reduce_tail

  subroutine babai(g,star,h,target,a)
    integer, intent(in) :: g(:,:),star(:,:),h(:),target(:)
    integer, intent(out) :: a(:)
    integer :: residual(size(target)),i,k,c
    residual=target
    do i=size(a),1,-1
      c=rf(ra(rd(qdot(residual,star(:,i)),h(i)),rd(r1,ri(2_ik))))
      a(i)=c
      do k=1,size(target)
        residual(k)=rs(residual(k),rm(c,g(k,i)))
      end do
    end do
  end subroutine babai
end module sp_lattice
