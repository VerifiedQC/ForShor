program frontend_errors
  use sp_arithmetic, only: ik,leaf_cost
  use sp_outer, only: optimize_catalogue,no_cap_dominates
  implicit none
  integer :: entries(5,1),path(6,10),depth,status
  integer(ik) :: cost,counters(7)
  if (.not.no_cap_dominates((/4,4,36/),(/4,3,35/))) stop 7
  if (.not.no_cap_dominates((/4,4,36/),(/4,4,36/))) stop 8
  if (no_cap_dominates((/4,4,35/),(/4,4,36/))) stop 9
  if (no_cap_dominates((/3,4,36/),(/4,4,36/))) stop 10
  if (no_cap_dominates((/4,3,36/),(/4,4,36/))) stop 11
  if (no_cap_dominates((/-1,-1,-1/),(/0,0,0/))) stop 12
  entries(:,1)=(/3,1,8,2,4/)
  path=0
  depth=0
  cost=leaf_cost(1_ik,10)
  call optimize_catalogue(10,3,entries,cost,path,depth,counters(1:6),status)
  if (status/=4) stop 1
  entries(2,1)=3
  call optimize_catalogue(10,3,entries,cost,path,depth,counters,status)
  if (status/=4) stop 2
  entries(2,1)=1
  call optimize_catalogue(10,3,entries,cost,path(:,1:1),depth,counters,status)
  if (status/=4) stop 3
  call optimize_catalogue(0,3,entries,cost,path,depth,counters,status)
  if (status/=4) stop 4
  entries(5,1)=1
  call optimize_catalogue(10,3,entries,cost,path,depth,counters,status)
  if (status/=4) stop 5
  entries(5,1)=4
  ! Sequential calls exercise cleanup, pointer initialization and reset.
  call optimize_catalogue(10,3,entries,cost,path,depth,counters,status)
  if (status/=0) stop 6
  write(*,*) 'PASS frontend invalid-input statuses and recovery'
end program frontend_errors
