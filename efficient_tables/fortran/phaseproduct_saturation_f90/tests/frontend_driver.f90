program frontend_driver
  use sp_arithmetic, only: ik,leaf_cost
  use sp_outer, only: optimize_catalogue
  implicit none
  integer :: n,k,m,i,depth,status,ios
  integer, allocatable :: entries(:,:),path(:,:)
  integer(ik) :: cost,counters(7)
  do
    read(*,*,iostat=ios) n,k,m
    if (ios/=0) exit
    allocate(entries(5,m),path(6,n))
    do i=1,m
      read(*,*) entries(:,i)
    end do
    depth=0
    cost=leaf_cost(1_ik,n)
    path=0
    call optimize_catalogue(n,k,entries,cost,path,depth,counters,status)
    write(*,*) 'RESULT ',status,cost,depth,counters
    do i=1,depth
      write(*,*) 'PATH ',path(:,i)
    end do
    deallocate(entries,path)
  end do
end program frontend_driver
