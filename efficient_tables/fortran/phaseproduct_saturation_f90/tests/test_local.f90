program test_local
  use sp_oracle
  use sp_threshold
  implicit none
  integer, parameter :: wide=selected_int_kind(18)
  integer :: ops(5,2048),nop,status,c,a,b,k,states,i,rc
  integer(wide) :: theta,counters(2),top
  do k=2,8
    call paired_constructor(k,ops,nop,status,c,a,b)
    if (status/=0) stop 1
    if (c>6*k*k .or. a>8*k*k .or. b>8*k*k) stop 2
    call cap_replay(k,a,b,ops(:,1:nop),status,rc)
    if (status/=0 .or. rc/=c) stop 3
    print *, 'CTOR',k,nop,c,a,b
    do i=1,nop
      print *, 'OP',ops(:,i)
    end do
  end do
  call cap_decide_generic(2,2,2,3,status,ops,nop,states)
  if (status/=1) stop 4
  print *, 'GENERIC_K2_C3',states
  call cap_decide_generic(2,2,2,4,status,ops,nop,states)
  if (status/=0 .or. nop/=2) stop 5
  call cap_replay(2,2,2,ops(:,1:nop),status,c)
  if (status/=0 .or. c/=4) stop 6
  print *, 'GENERIC_K2_C4',states
  call cap_decide_generic(2,1,1,4,status,ops,nop,states)
  if (status/=1) stop 7
  print *, 'GENERIC_K2_A1',states
  call cap_decide(3,2,2,4,status,ops,nop,states)
  if (status/=1) stop 8
  print *, 'PRUNED_K3_C4',states
  call cap_decide_generic(3,2,2,4,status,ops,nop,states)
  if (status/=1) stop 9
  print *, 'GENERIC_K3_C4',states
  call threshold_search(2,1,4,huge(theta),theta,ops,nop,status,counters)
  if (status/=0 .or. theta/=3_wide) stop 10
  call threshold_search(2,1,3,100_wide,theta,ops,nop,status,counters)
  if (status/=1 .or. theta/=-1_wide) stop 11
  call threshold_search(3,0,0,5_wide,theta,ops,nop,status,counters)
  if (status/=1 .or. theta/=-1_wide) stop 12
  call threshold_search(3,2,1,3_wide,theta,ops,nop,status,counters)
  if (status/=1 .or. theta/=-1_wide) stop 13
  call saturation_cap(2,huge(theta),status,top)
  if (status/=0 .or. top/=huge(theta)-2_wide) stop 14
  print *, 'LOCAL_TESTS_PASS'
end program test_local
