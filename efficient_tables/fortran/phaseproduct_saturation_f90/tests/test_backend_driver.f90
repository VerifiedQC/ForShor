program test_backend_driver
  use sp_ilp
  implicit none
  integer(ik), allocatable :: a(:,:),b(:),x(:)
  integer, allocatable :: f(:,:),g(:,:),u(:,:)
  integer(ik), allocatable :: gi(:,:),ui(:,:)
  type(ilp_stats) :: stats
  type(lattice_stats) :: ls
  integer :: cases,mode,m,n,i,j,k,st,p,q,v,w,s
  integer(ik) :: vv
  read(*,*) mode,cases
  if(mode==3) then
    do k=0,1200
      r_fail_after=k
      call r_start()
      p=ri(123456789_ik);q=ri(9999997_ik)
      v=rd(rm(p,p),q);w=ra(v,rd(q,p));s=rf(w)
      call r_finish()
      if(r_status/=0.and.r_status/=3) stop 15
    end do
    r_fail_after=-1
    print *, 'ALLOCATION_FAILURE_PASS'
    stop
  end if
  if(mode==4) then
    allocate(a(4,2),b(4),x(2))
    a=0_ik; a(1,1)=1_ik; a(2,1)=-1_ik; a(3,2)=1_ik; a(4,2)=-1_ik; b=1_ik
    do k=0,20000,337
      r_fail_after=k
      call ilp_feasible(a,b,x,st,stats)
      if(st/=0.and.st/=3) stop 16
    end do
    r_fail_after=-1
    print *, 'ILP_ALLOCATION_FAILURE_PASS'
    stop
  end if
  if(mode==2) then
    call r_start()
    p=ri(2_ik); q=r1
    do i=1,256
      q=rm(q,p)
    end do
    v=rd(ra(q,r1),q)
    if(rc(rs(v,r1),rd(r1,q))/=0) stop 10
    if(rc(rf(rd(ri(-7_ik),ri(3_ik))),ri(-3_ik))/=0) stop 11
    if(rc(rroot(rs(rm(q,q),r1)),q)/=0) stop 12
    if(rc(rroot(ra(rm(q,q),r1)),ra(q,r1))/=0) stop 13
    do i=-30,30
      do j=1,31
        p=rd(ri(int(i,ik)),ri(int(j,ik)))
        if(rc(rm(p,ri(int(j,ik))),ri(int(i,ik)))/=0) stop 14
      end do
    end do
    print *, 'ARITHMETIC_PASS',r_status
    call r_finish()
    stop
  end if
  do k=1,cases
    read(*,*) m,n
    allocate(a(m,n),b(m),x(n))
    if(mode==0) then
      do i=1,m
        read(*,*) a(i,:),b(i)
      end do
      call ilp_feasible(a,b,x,st,stats)
      write(*,*) st,x,stats%nodes,stats%vertices,stats%simplex_exchanges, &
        stats%suffix_candidates,stats%lattice%lll_swaps,stats%lattice%hkz_calls, &
        stats%lattice%svp_candidates
    else
      do i=1,m
        read(*,*) a(i,:)
      end do
      call r_start()
      ls%lll_swaps=0_ik; ls%hkz_calls=0_ik; ls%svp_candidates=0_ik
      allocate(f(m,n),g(m,n),u(n,n),gi(m,n),ui(n,n))
      do i=1,m
        do j=1,n
          f(i,j)=ri(a(i,j))
        end do
      end do
      call hkz(f,g,u,ls)
      do i=1,m
        do j=1,n
          gi(i,j)=rtoi(g(i,j),st)
        end do
      end do
      do i=1,n
        do j=1,n
          ui(i,j)=rtoi(u(i,j),st)
        end do
      end do
      write(*,*) r_status,((gi(i,j),j=1,n),i=1,m),((ui(i,j),j=1,n),i=1,n)
      call r_finish()
      deallocate(f,g,u,gi,ui)
    end if
    deallocate(a,b,x)
  end do
end program test_backend_driver
