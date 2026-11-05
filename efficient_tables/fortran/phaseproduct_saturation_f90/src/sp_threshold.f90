! Exact saturation threshold driver, theorem Section 7 (2026-10-15T190800).
! Paired constructor is a direct port of f2_bridge_witness.py: paired/build/inv.
module sp_threshold
  use sp_oracle, only: cap_decide, cap_replay, replay_profile
  implicit none
  private
  integer, parameter :: wide=selected_int_kind(18)
  public :: threshold_search, paired_constructor, saturation_cap
contains
  ! theta=-1,status=1 means no threshold <= n-2. Errors are 2 (range)
  ! and 3 (allocation/invalid). counters = (decision calls, retained states).
  subroutine threshold_search(k,d,C,n,theta,ops,nops,status,counters)
    integer, intent(in) :: k,d,C
    integer(wide), intent(in) :: n
    integer(wide), intent(out) :: theta,counters(2)
    integer, intent(out) :: ops(:,:),nops,status
    integer, allocatable :: ctor(:,:),trial(:,:)
    integer :: c0,a0,b0,nctor,err,lo,hi,mid,ntrial,states,rc
    integer(wide) :: kk,bound,top,maxcharge,astar
    theta=-1_wide
    counters=0_wide
    nops=0
    ops=0
    status=3
    if (k<2 .or. d<0 .or. d>=k .or. C<0 .or. n<0_wide) return
    if (size(ops,1)/=5) return
    kk=int(k,wide)*int(k,wide)
    maxcharge=sat_mul(sat_mul(27_wide,kk,int(huge(C),wide)),int(k,wide),int(huge(C),wide))
    if (int(C,wide)>maxcharge) return
    status=1
    if (n<2_wide+int(d,wide)) return
    if (k==2) then
      if (C<4) return
      top=int(d,wide)+2_wide
      if (top>n-2_wide) return
      status=2
      if (size(ops,2)<2) return
      ops(:,1)=(/1,1,2,-1,0/)
      ops(:,2)=(/1,1,2,1,0/)
      nops=2
      theta=top
      status=0
      return
    end if
    status=2
    bound=sat_mul(12_wide,kk,int(huge(C),wide))
    if (bound==int(huge(C),wide)) return
    allocate(ctor(5,int(bound)),trial(5,size(ops,2)),stat=err)
    if (err/=0) then
      status=3
      go to 9000
    end if
    call paired_constructor(k,ctor,nctor,status,c0,a0,b0)
    if (status/=0) go to 9000
    if (C>=c0) then
      astar=max(int(a0,wide),int(b0,wide)+int(d,wide))
      top=min(n-2_wide,astar)
    else
      call saturation_cap(k,n,status,top)
      if (status/=0) go to 9000
    end if
    ! Arithmetic limits are never returned as mathematical infeasibility.
    status=2
    if (top>int(huge(hi)-k+1,wide)) go to 9000
    hi=int(top)
    lo=d
    if (C>=c0 .and. top>=astar) then
      call cap_decide(k,hi,hi-d,C,rc,trial,ntrial,states,ctor(:,1:nctor))
    else
      call cap_decide(k,hi,hi-d,C,rc,trial,ntrial,states)
    end if
    call accumulate(states)
    if (rc/=0) then
      status=rc
      go to 9000
    end if
    nops=ntrial
    ops(:,1:nops)=trial(:,1:nops)
    do while(lo<hi)
      mid=lo+(hi-lo)/2
      call cap_decide(k,mid,mid-d,C,rc,trial,ntrial,states)
      call accumulate(states)
      if (rc==0) then
        hi=mid
        nops=ntrial
        ops(:,1:nops)=trial(:,1:nops)
      else if (rc==1) then
        lo=mid+1
      else
        status=rc
        nops=0
        ops=0
        go to 9000
      end if
    end do
    theta=int(hi,wide)
    status=0
9000 continue
    if (allocated(ctor)) deallocate(ctor)
    if (allocated(trial)) deallocate(trial)
    return
  contains
    subroutine accumulate(nstates)
      integer, intent(in) :: nstates
      counters(1)=counters(1)+1_wide
      counters(2)=sat_add(counters(2),int(nstates,wide),huge(counters(2)))
    end subroutine accumulate
  end subroutine threshold_search

  ! Compute min(n-2,(m+1)m!B**m) without constructing huge integers.
  ! m=6k^2, B=8k^2. Early saturation depends only on exact comparisons.
  subroutine saturation_cap(k,n,status,T)
    integer, intent(in) :: k
    integer(wide), intent(in) :: n
    integer, intent(out) :: status
    integer(wide), intent(out) :: T
    integer(wide) :: kk,m,B,i,limit
    status=3
    T=-1_wide
    if (k<2 .or. n<2_wide) return
    status=0
    limit=n-2_wide
    kk=int(k,wide)*int(k,wide)
    m=sat_mul(6_wide,kk,huge(m))
    B=sat_mul(8_wide,kk,huge(B))
    T=min(limit,sat_add(m,1_wide,limit))
    i=1_wide
    do while(i<=m .and. T<limit)
      T=sat_mul(T,i,limit)
      T=sat_mul(T,B,limit)
      i=i+1_wide
    end do
  end subroutine saturation_cap

  integer(wide) function sat_mul(x,y,limit)
    integer(wide), intent(in) :: x,y,limit
    sat_mul=0_wide
    if (x==0_wide .or. y==0_wide .or. limit==0_wide) return
    if (x>limit/y) then
      sat_mul=limit
    else
      sat_mul=x*y
    end if
  end function sat_mul

  integer(wide) function sat_add(x,y,limit)
    integer(wide), intent(in) :: x,y,limit
    if (x>=limit .or. y>=limit-x) then
      sat_add=limit
    else
      sat_add=x+y
    end if
  end function sat_add

  subroutine paired_constructor(k,ops,nops,status,c0,a0,b0)
    integer, intent(in) :: k
    integer, intent(out) :: ops(:,:),nops,status,c0,a0,b0
    integer :: nt,ix,e,j,shift,first,last,sg,step
    logical :: fraction,failed
    integer(wide) :: kk
    nops=0
    ops=0
    status=3
    c0=-1
    a0=-1
    b0=-1
    if (k<2 .or. size(ops,1)/=5) return
    kk=int(k,wide)*int(k,wide)
    status=2
    if (kk>int(huge(nt),wide)/int(12,wide)) return
    nt=2*k-1
    failed=.false.
    ix=3
    do while(ix<=nt)
      e=0
      fraction=.false.
      if (ix>=5) then
        e=(ix-5)/4+1
        fraction=mod(ix-5,4)<2
      end if
      first=nops+1
      if (ix==nt) then
        ! Last singleton is the negative point. Preserve repository signs.
        shift=0
        if (fraction) shift=e*(k-1)
        if (shift>0) call emit((/2,1,0,0,shift/))
        if (fraction .and. mod(k,2)==0) call emit((/4,1,0,0,0/))
        do j=2,k
          step=j-1
          if (fraction) step=k-j
          sg=1
          if (mod(step,2)==1) sg=-1
          call emit((/1,1,j,sg,e*step/))
        end do
        last=nops
        call invert(first,last)
        ix=ix+1
      else
        ! Prepare positive-denominator even/odd partial sums in rows 1,2.
        do j=1,2
          step=j-1
          if (fraction) step=k-j
          shift=e*step
          if (shift>0) call emit((/2,j,0,0,shift/))
        end do
        do j=3,k
          step=j-1
          if (fraction) step=k-j
          call emit((/1,mod(j-1,2)+1,j,1,e*step/))
        end do
        last=nops
        call emit((/1,1,2,1,0/))
        call emit((/1,1,2,-1,1/))
        ! Negative reciprocals differ by an overall sign for even k.
        if (fraction .and. mod(k,2)==0) then
          call emit((/4,1,0,0,0/))
          call emit((/4,1,0,0,0/))
        end if
        call emit((/1,1,2,1,0/))
        call invert(first,last)
        ix=ix+2
      end if
      if (failed) then
        status=2
        return
      end if
    end do
    call replay_profile(k,ops(:,1:nops),status,c0,a0,b0)
    return
  contains
    subroutine emit(op)
      integer, intent(in) :: op(5)
      if (failed) return
      if (nops==size(ops,2)) then
        failed=.true.
        return
      end if
      nops=nops+1
      ops(:,nops)=op
    end subroutine emit

    subroutine invert(start,finish)
      integer, intent(in) :: start,finish
      integer :: i,op(5)
      do i=finish,start,-1
        if (failed) return
        op=ops(:,i)
        if (op(1)==1) then
          op(4)=-op(4)
        else if (op(1)==2) then
          op(1)=3
        else if (op(1)==3) then
          op(1)=2
        end if
        call emit(op)
      end do
    end subroutine invert
  end subroutine paired_constructor
end module sp_threshold
