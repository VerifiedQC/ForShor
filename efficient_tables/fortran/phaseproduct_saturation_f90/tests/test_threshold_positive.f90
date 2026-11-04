! Independent review regression: successful nontrivial threshold and API edges.
program test_threshold_positive
  use sp_oracle
  use sp_threshold
  implicit none
  integer, parameter :: wide=selected_int_kind(18)
  integer :: ops(5,4096),bad(4,8),nops,status,states,c,a,b,i
  integer(wide) :: theta,counters(2),top
  call threshold_search(huge(0),0,0,huge(theta),theta,ops,nops,status,counters)
  if (status/=2 .or. theta/=-1_wide) stop 1
  call threshold_search(-huge(0)-1,0,0,huge(theta),theta,ops,nops,status,counters)
  if (status/=3) stop 2
  call threshold_search(2,0,huge(0),100_wide,theta,ops,nops,status,counters)
  if (status/=3) stop 3
  call threshold_search(2,0,4,100_wide,theta,bad,nops,status,counters)
  if (status/=3) stop 4
  call paired_constructor(huge(0),ops,nops,status,c,a,b)
  if (status/=2) stop 5
  call replay_profile(huge(0),ops,status,c,a,b)
  if (status/=2) stop 6
  call cap_decide(huge(0),0,0,0,status,ops,nops,states)
  if (status/=2) stop 7
  call cap_decide(65537,0,0,0,status,ops,nops,states)
  if (status/=1) stop 8
  call cap_decide(2,huge(0),huge(0),4,status,ops,nops,states)
  if (status/=2) stop 9
  call cap_replay(huge(0),0,0,ops,status,c)
  if (status/=2) stop 10
  call saturation_cap(huge(0),huge(theta),status,top)
  if (status/=0 .or. top/=huge(theta)-2_wide) stop 11
  print *, 'EDGE_REVIEW_PASS'

  call threshold_search(3,1,11,8_wide,theta,ops,nops,status,counters)
  print *, 'THRESHOLD',status,theta,nops,counters
  if (status/=0 .or. theta/=6_wide) stop 12
  do i=1,nops
    print *, 'OP',ops(:,i)
  end do
  call cap_replay(3,6,5,ops(:,1:nops),status,c)
  print *, 'REPLAY',status,c
  if (status/=0 .or. c>11) stop 13
  call cap_decide(3,5,4,11,status,ops,nops,states)
  print *, 'CAP5',status,nops,states
  if (status/=1 .or. nops/=0) stop 14
  print *, 'THRESHOLD_POSITIVE_PASS'
end program test_threshold_positive
