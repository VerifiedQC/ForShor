! Coupled saturated catalogue / decorated-word Kannan frontend.
module sp_outer
  use sp_arithmetic, only: ik, INF, sat_add, sat_mul, leaf_cost, child_width
  use sp_threshold, only: threshold_search
  use sp_oracle, only: cap_replay
  use sp_ilp, only: ilp_feasible, ilp_stats
  implicit none
  private
  public :: solve_pp, optimize_catalogue, no_cap_dominates
  ! Counters: decorated prefixes, ILP calls, HKZ calls, ILP nodes,
  ! ILP vertices, suffix assignments, interval/bound prunes.
  integer :: arithmetic_status=0
  type witness
    integer, pointer :: ops(:,:)
  end type witness
  type bound_node
    integer :: w
    integer(ik) :: mult,value,prefix
    type(bound_node), pointer :: next
  end type bound_node
  type(bound_node), pointer :: bounds
  integer :: limit_k,bound_count
  integer(ik) :: upper,bound_hits
  integer, allocatable :: mass_log(:,:)
contains
  logical function no_cap_dominates(known,asked)
    integer, intent(in) :: known(3),asked(3)
    ! Triples are (zero cap, shifted cap, charge). A NO for a superset
    ! of allowed words certifies NO for the subset, never conversely.
    no_cap_dominates=all(known>=asked)
  end function no_cap_dominates

  subroutine fail(message)
    character(len=*), intent(in) :: message
    write(*,*) 'ERROR ',message
    stop 1
  end subroutine fail

  function add(x,y) result(z)
    integer(ik), intent(in) :: x,y
    integer(ik) :: z
    z=0_ik
    if (y>0_ik) then
      if (x>INF-y) then
        arithmetic_status=2
        return
      end if
    else if (y<0_ik) then
      if (x<(-INF)-y) then
        arithmetic_status=2
        return
      end if
    end if
    z=x+y
  end function add

  function mul(x,y) result(z)
    integer(ik), intent(in) :: x,y
    integer(ik) :: z
    z=0_ik
    if (x==0_ik .or. y==0_ik) return
    ! All frontend encodings deliberately use the symmetric native range.
    if (x< -INF .or. y< -INF) then
      arithmetic_status=2
      return
    end if
    if (abs(x)>INF/abs(y)) then
      arithmetic_status=2
      return
    end if
    z=x*y
  end function mul

  function own_cost(mult,w,c) result(z)
    integer(ik), intent(in) :: mult
    integer, intent(in) :: w,c
    integer(ik) :: z
    z=sat_mul(sat_mul(sat_mul(8_ik,mult),int(w-1,ik)),int(c,ik))
  end function own_cost

  subroutine tick(x,y)
    integer(ik), intent(inout) :: x
    integer(ik), intent(in) :: y
    x=sat_add(x,y)
  end subroutine tick

  ! The Bellman mass bound below is ported from pp_solver (preserved sibling).
  ! TWO_CAP_BRIDGE and MARKER_DEPARTURE justify 4k-4 and the mass width floor.
  function target_mass_log(k,r) result(bits)
    integer, intent(in) :: k,r
    integer :: bits,t,j,e,q,kind
    integer(ik) :: mass,largest,term,exponent,remaining
    integer(ik), parameter :: ceiling=1152921504606846976_ik
    largest=1_ik
    do t=3,2*k-1
      if (t<=4) then
        e=0
        kind=0
      else
        q=t-5
        e=q/4+1
        kind=0
        if (mod(q,4)<2) kind=1
      end if
      mass=0_ik
      do j=0,k-1
        if (kind==0) then
          exponent=int(e,ik)*int(j,ik)
        else
          exponent=int(e,ik)*int(k-1-j,ik)
        end if
        if (j==k-1) exponent=exponent+int(r,ik)
        if (exponent>=60_ik) then
          term=ceiling
        else
          term=2_ik**int(exponent)
        end if
        mass=min(ceiling,mass+term)
      end do
      largest=max(largest,mass)
    end do
    bits=0
    remaining=largest-1_ik
    do while(remaining>0_ik)
      bits=bits+1
      remaining=remaining/2_ik
    end do
  end function target_mass_log

  recursive function continuation_bound(w,mult) result(value)
    integer, intent(in) :: w
    integer(ik), intent(in) :: mult
    integer(ik) :: value,own,next_mult,trial
    integer :: k,child,minimum,err
    type(bound_node), pointer :: node
    value=upper
    if (mult>upper/5_ik) return
    node=>bounds
    do while(associated(node))
      if (node%w==w .and. node%mult==mult) then
        value=node%value
        call tick(bound_hits,1_ik)
        return
      end if
      node=>node%next
    end do
    value=min(upper,leaf_cost(mult,w))
    do k=2,min(limit_k,w)
      minimum=w/k+2+mass_log(mod(w,k),k)
      next_mult=sat_mul(mult,int(2*k-1,ik))
      do child=minimum,w-1
        own=own_cost(mult,child,4*k-4)
        if (own>=value) exit
        trial=sat_add(own,continuation_bound(child,next_mult))
        value=min(value,trial)
      end do
    end do
    allocate(node,stat=err)
    if (err/=0) call fail('cannot allocate relaxed Bellman state')
    node%w=w
    node%mult=mult
    node%value=value
    node%prefix=INF
    node%next=>bounds
    bounds=>node
    if (bound_count==huge(0)) call fail('bound state index range')
    bound_count=bound_count+1
  end function continuation_bound

  subroutine solve_pp(n,kmax,use_bounds)
    integer, intent(in) :: n,kmax
    logical, intent(in) :: use_bounds
    integer, allocatable :: best_path(:,:),path(:,:),amax(:,:),cmax(:,:),entries(:,:),larger(:,:)
    integer, allocatable :: theta(:),query_ops(:,:),padded(:,:),negative(:,:)
    type(witness), allocatable :: words(:),more_words(:),query_words(:)
    type(bound_node), pointer :: node,next_node,target
    integer :: err,k,d,r,w,child,a,b,depth,best_depth,j,id,capacity,count,st,charge,e,base
    integer :: first_charge,last_charge,ray_a,ray_k,ray_d,nops,start_tick,end_tick,rate,tick_max
    integer(ik) :: best_cost,total,mult,next_mult,root_bound,tail,own,trial,denom,candidate,maximum
    integer(ik) :: seed_nodes,counters(7),queries,oracle_calls,oracle_states,peak_states,counts(2),th
    integer(ik) :: threshold_hits
    integer(ik) :: elapsed_ticks
    real(kind=selected_real_kind(12)) :: seconds
    nullify(bounds,node,next_node,target)
    call system_clock(start_tick,rate,tick_max)
    if (n<1 .or. kmax<1) call fail('n and kmax must be positive')
    upper=leaf_cost(1_ik,n)
    if (upper==INF) call fail('root stop cost exceeds exact native range')
    limit_k=min(n,kmax)
    arithmetic_status=0
    best_cost=upper
    best_depth=0
    bound_count=0
    bound_hits=0_ik
    seed_nodes=0_ik
    counters=0_ik
    queries=0_ik
    oracle_calls=0_ik
    oracle_states=0_ik
    peak_states=0_ik
    threshold_hits=0_ik
    count=0
    capacity=16
    allocate(best_path(6,n),path(6,n),amax(limit_k,limit_k),cmax(limit_k,limit_k), &
      mass_log(0:limit_k-1,limit_k),entries(5,capacity),words(capacity),negative(3,limit_k),stat=err)
    if (err/=0) call fail('cannot allocate frontend storage')
    do j=1,capacity
      nullify(words(j)%ops)
    end do
    best_path=0
    negative=-1
    ! Complete single-arity k=2 specialization, with every stopping level.
    if (limit_k>=2) then
      do a=2,n-2
        do d=0,1
          b=a-d
          if (b<2) cycle
          w=n
          mult=1_ik
          total=0_ik
          depth=0
          do
            call tick(seed_nodes,1_ik)
            trial=sat_add(total,leaf_cost(mult,w))
            if (trial<best_cost) then
              best_cost=trial
              best_depth=depth
              best_path(:,1:depth)=path(:,1:depth)
            end if
            child=child_width(w,2,a,b)
            if (child>=w) exit
            own=own_cost(mult,child,4)
            total=sat_add(total,own)
            if (total>=best_cost) exit
            next_mult=sat_mul(mult,3_ik)
            if (next_mult>best_cost/5_ik) exit
            depth=depth+1
            path(:,depth)=(/2,4,a,b,child,-1/)
            w=child
            mult=next_mult
          end do
        end do
      end do
    end if
    root_bound=0_ik
    if (limit_k<=2) root_bound=best_cost
    if (use_bounds .and. limit_k>2) then
      do k=2,limit_k
        do r=0,k-1
          mass_log(r,k)=target_mass_log(k,r)
        end do
      end do
      root_bound=continuation_bound(n,1_ik)
    end if
    if (limit_k>2 .and. root_bound<best_cost) then
      amax=-1
      cmax=0
      if (use_bounds) then
        ! All same-width predecessors are already processed. Prefixes use
        ! the least relaxed cost, independent of the policy's sharing.
        node=>bounds
        do while(associated(node))
          if (node%w==n .and. node%mult==1_ik) node%prefix=0_ik
          node=>node%next
        end do
        do w=n,1,-1
          node=>bounds
          do while(associated(node))
            if (node%w==w .and. node%prefix<best_cost) then
              do k=2,min(limit_k,w)
                next_mult=sat_mul(node%mult,int(2*k-1,ik))
                do child=w/k+2+mass_log(mod(w,k),k),w-1
                  own=own_cost(node%mult,child,4*k-4)
                  tail=continuation_bound(child,next_mult)
                  trial=sat_add(sat_add(node%prefix,own),tail)
                  if (trial>=best_cost) cycle
                  target=>bounds
                  do while(associated(target))
                    if (target%w==child .and. target%mult==next_mult) exit
                    target=>target%next
                  end do
                  if (.not.associated(target)) call fail('missing competitive relaxed DAG state')
                  target%prefix=min(target%prefix,sat_add(node%prefix,own))
                  denom=own_cost(node%mult,child,1)
                  candidate=(best_cost-1_ik-node%prefix-tail)/denom
                  do d=0,k-1
                    a=child-w/k-1-max(0,mod(w,k)-d)
                    if (a<d) cycle
                    amax(d+1,k)=max(amax(d+1,k),a)
                    cmax(d+1,k)=int(min(int(huge(0),ik),max(int(cmax(d+1,k),ik),candidate)))
                  end do
                end do
              end do
            end if
            node=>node%next
          end do
        end do
      else
        do k=2,limit_k
          do d=0,k-1
            do w=1,n
              a=w-2-w/k-max(0,mod(w,k)-d)
              amax(d+1,k)=max(amax(d+1,k),a)
            end do
            cmax(d+1,k)=huge(0)
          end do
        end do
      end if
      do k=2,limit_k
        do d=0,k-1
          maximum=sat_mul(27_ik,sat_mul(int(k,ik),sat_mul(int(k,ik),int(k,ik))))
          if (maximum>int(huge(0)-1,ik)) call fail('charge catalogue index range')
          ray_a=amax(d+1,k)
          if (ray_a<d) cycle
          ! TWO_CAP_BRIDGE: scanner-sum increments count charged gates;
          ! identity determinant cancels net shifts, giving charge<=3*k*a.
          last_charge=int(min(maximum,int(cmax(d+1,k),ik),sat_mul(3_ik*int(k,ik),int(ray_a,ik))))
          first_charge=4*k-4
          if (last_charge<first_charge) cycle
          ray_k=k
          ray_d=d
          maximum=sat_add(sat_mul(81_ik,sat_mul(int(k,ik),sat_mul(int(k,ik),int(k,ik)))),int(2*k-1,ik))
          if (maximum>int(huge(0),ik)) call fail('witness storage index range')
          allocate(theta(first_charge-1:last_charge),query_words(first_charge-1:last_charge), &
            query_ops(5,int(maximum)),stat=err)
          if (err/=0) call fail('cannot allocate threshold cache')
          do j=first_charge-1,last_charge
            nullify(query_words(j)%ops)
          end do
          theta=-1
          theta(first_charge-1)=ray_a+1
          call query(last_charge)
          call staircase(first_charge-1,last_charge)
          do j=first_charge-1,last_charge
            if (associated(query_words(j)%ops)) deallocate(query_words(j)%ops)
          end do
          deallocate(theta,query_words,query_ops)
        end do
      end do
      call optimize_catalogue(n,limit_k,entries(:,1:count),best_cost,best_path,best_depth,counters,st)
      if (st/=0) call fail('coupled Kannan optimizer returned a non-answer')
    end if
    ! Verify every padded literal table before printing any certificate.
    do k=2,limit_k
      id=0
      do j=1,best_depth
        if (best_path(1,j)==k) id=j
      end do
      if (id==0) cycle
      call padded_table(id)
      call cap_replay(k,best_path(3,id),best_path(4,id),padded,st,charge)
      if (st/=0 .or. charge/=best_path(2,id)) call fail('final literal replay failed')
      deallocate(padded)
    end do
    call system_clock(end_tick)
    elapsed_ticks=int(end_tick,ik)-int(start_tick,ik)
    if (elapsed_ticks<0_ik) elapsed_ticks=elapsed_ticks+int(tick_max,ik)+1_ik
    seconds=real(elapsed_ticks,kind=selected_real_kind(12))/real(max(1,rate),kind=selected_real_kind(12))
    write(*,*) 'STATUS OPTIMAL'
    write(*,*) 'ALGORITHM SATURATION_DECORATED_KANNAN'
    write(*,*) 'COST ',best_cost
    write(*,*) 'LOWER_BOUND ',best_cost
    write(*,*) 'ROOT_RELAXATION ',root_bound
    write(*,*) 'N ',n
    write(*,*) 'KMAX ',kmax
    write(*,*) 'EXACT_K2_SHORTCUT ',limit_k<=2
    write(*,*) 'NODES ',counters(1)
    write(*,*) 'SEED_NODES ',seed_nodes
    write(*,*) 'CAP_QUERIES ',oracle_calls
    write(*,*) 'THRESHOLD_QUERIES ',queries
    write(*,*) 'THRESHOLD_CACHE_HITS ',threshold_hits
    write(*,*) 'ORACLE_STATES ',oracle_states
    write(*,*) 'PEAK_ORACLE_STATES ',peak_states
    write(*,*) 'PEAK_ORACLE_STATES_UPPER_BOUND T'
    write(*,*) 'BOUND_STATES ',bound_count
    write(*,*) 'BOUND_HITS ',bound_hits
    write(*,*) 'ILP_CALLS ',counters(2)
    write(*,*) 'HKZ_CALLS ',counters(3)
    write(*,*) 'ILP_NODES ',counters(4)
    write(*,*) 'ILP_VERTICES ',counters(5)
    write(*,*) 'ILP_SUFFIX_ASSIGNMENTS ',counters(6)
    write(*,*) 'CATALOGUE_ENTRIES ',count
    write(*,*) 'ELAPSED_SECONDS ',seconds
    write(*,*) 'CLOCK_TICKS_PER_SECOND ',rate
    mult=1_ik
    do j=1,best_depth
      write(*,*) 'LEVEL ',best_path(1:5,j),mult
      mult=sat_mul(mult,int(2*best_path(1,j)-1,ik))
    end do
    do k=2,limit_k
      id=0
      do j=1,best_depth
        if (best_path(1,j)==k) id=j
      end do
      if (id==0) cycle
      e=best_path(6,id)
      base=2
      if (e>0) base=size(words(e)%ops,2)
      write(*,*) 'TABLE ',k,best_path(2:4,id),base+4
      write(*,*) 'OP ',2,1,0,0,best_path(3,id)
      write(*,*) 'OP ',3,1,0,0,best_path(3,id)
      write(*,*) 'OP ',2,k,0,0,best_path(4,id)
      write(*,*) 'OP ',3,k,0,0,best_path(4,id)
      if (e>0) then
        do j=1,base
          write(*,*) 'OP ',words(e)%ops(:,j)
        end do
      else
        write(*,*) 'OP ',1,1,2,-1,0
        write(*,*) 'OP ',1,1,2,1,0
      end if
      write(*,*) 'END_TABLE'
    end do
    do j=1,capacity
      if (associated(words(j)%ops)) deallocate(words(j)%ops)
    end do
    do while(associated(bounds))
      next_node=>bounds%next
      deallocate(bounds)
      bounds=>next_node
    end do
    deallocate(best_path,path,amax,cmax,mass_log,entries,words,negative)
  contains
    subroutine query(c)
      integer, intent(in) :: c
      if (theta(c)>=0) return
      ! A certified NO for larger caps and charge implies this query's NO.
      ! Keep the original dominating triple when reusing it across rays.
      if (no_cap_dominates(negative(:,ray_k),(/ray_a,ray_a-ray_d,c/))) then
        theta(c)=ray_a+1
        call tick(threshold_hits,1_ik)
        return
      end if
      call threshold_search(ray_k,ray_d,c,int(ray_a,ik)+2_ik,th,query_ops,nops,st,counts)
      call tick(queries,1_ik)
      call tick(oracle_calls,counts(1))
      call tick(oracle_states,counts(2))
      ! Threshold API exposes accumulated retained states per query, not
      ! the peak of its inner decisions. This is a conservative peak bound.
      peak_states=max(peak_states,counts(2))
      if (st==1) then
        theta(c)=ray_a+1
        negative(:,ray_k)=(/ray_a,ray_a-ray_d,c/)
      else if (st==0) then
        if (th<0_ik .or. th>int(ray_a,ik)) call fail('threshold outside truncation')
        theta(c)=int(th)
        allocate(query_words(c)%ops(5,nops),stat=err)
        if (err/=0) call fail('cannot retain threshold witness')
        query_words(c)%ops=query_ops(:,1:nops)
      else
        call fail('saturation threshold returned a non-answer')
      end if
    end subroutine query

    recursive subroutine staircase(left,right)
      integer, intent(in) :: left,right
      integer :: middle
      if (theta(left)==theta(right)) return
      if (theta(left)<theta(right)) call fail('nonmonotone threshold oracle')
      if (right-left==1) then
        call append_entry(right,theta(right),theta(left)-1)
      else
        middle=left+(right-left)/2
        call query(middle)
        call staircase(left,middle)
        call staircase(middle,right)
      end if
    end subroutine staircase

    subroutine append_entry(c,low,high)
      integer, intent(in) :: c,low,high
      integer :: i,new_capacity
      call cap_replay(ray_k,low,low-ray_d,query_words(c)%ops,st,charge)
      if (st/=0 .or. charge/=c) call fail('threshold drop witness charge mismatch')
      if (count==capacity) then
        if (capacity>huge(0)/2) call fail('catalogue index range')
        new_capacity=2*capacity
        allocate(larger(5,new_capacity),more_words(new_capacity),stat=err)
        if (err/=0) call fail('cannot grow catalogue')
        do i=1,new_capacity
          nullify(more_words(i)%ops)
        end do
        larger=0
        larger(:,1:count)=entries(:,1:count)
        more_words(1:count)=words(1:count)
        deallocate(entries,words)
        allocate(entries(5,new_capacity),words(new_capacity),stat=err)
        if (err/=0) call fail('cannot relocate catalogue')
        entries=larger
        words=more_words
        deallocate(larger,more_words)
        capacity=new_capacity
      end if
      count=count+1
      entries(:,count)=(/ray_k,ray_d,c,low,high/)
      allocate(words(count)%ops(5,size(query_words(c)%ops,2)),stat=err)
      if (err/=0) call fail('cannot retain catalogue witness')
      words(count)%ops=query_words(c)%ops
    end subroutine append_entry

    subroutine padded_table(level)
      integer, intent(in) :: level
      integer :: e,base,a,b,k
      e=best_path(6,level)
      a=best_path(3,level)
      b=best_path(4,level)
      k=best_path(1,level)
      base=2
      if (e>0) base=size(words(e)%ops,2)
      allocate(padded(5,base+4),stat=err)
      if (err/=0) call fail('cannot allocate padded witness')
      padded(:,1)=(/2,1,0,0,a/)
      padded(:,2)=(/3,1,0,0,a/)
      padded(:,3)=(/2,k,0,0,b/)
      padded(:,4)=(/3,k,0,0,b/)
      if (e>0) then
        padded(:,5:base+4)=words(e)%ops
      else
        padded(:,5)=(/1,1,2,-1,0/)
        padded(:,6)=(/1,1,2,1,0/)
      end if
    end subroutine padded_table
  end subroutine solve_pp

  subroutine optimize_catalogue(n,kmax,entries,best_cost,best_path,best_depth,counters,status)
    integer, intent(in) :: n,kmax,entries(:,:)
    integer(ik), intent(inout) :: best_cost
    integer, intent(inout) :: best_path(:,:),best_depth
    integer(ik), intent(out) :: counters(:)
    integer, intent(out), optional :: status
    integer, allocatable :: ids(:),residues(:),var_for(:),used(:),lo(:),hi(:),trial_path(:,:)
    integer(ik), allocatable :: x(:,:),p(:),nn(:),amat(:,:),rhs(:),sol(:),saved(:)
    integer :: rc,err,maxdepth,k,e,old_status
    integer(ik) :: u,q
    type(bound_node), pointer :: cache,node,next_node
    nullify(cache,node,next_node)
    counters=0_ik
    rc=4
    old_status=arithmetic_status
    arithmetic_status=0
    if (n<1 .or. kmax<1 .or. size(entries,1)/=5 .or. size(counters)<7) go to 900
    if (size(best_path,1)/=6 .or. size(best_path,2)<n) go to 900
    if (best_depth<0 .or. best_depth>n .or. best_cost<0_ik) go to 900
    u=leaf_cost(1_ik,n)
    if (u==INF) then
      rc=2
      go to 900
    end if
    if (best_cost>u) go to 900
    do e=1,size(entries,2)
      k=entries(1,e)
      if (k<2 .or. k>kmax .or. k>n) go to 900
      if (entries(2,e)<0 .or. entries(2,e)>=k .or. entries(3,e)<1) go to 900
      if (entries(4,e)<entries(2,e) .or. entries(5,e)<entries(4,e)) go to 900
    end do
    maxdepth=0
    q=1_ik
    do while(q<=u/3_ik)
      maxdepth=maxdepth+1
      q=q*3_ik
    end do
    maxdepth=min(maxdepth,n-1)
    allocate(ids(maxdepth),residues(maxdepth),var_for(kmax),used(maxdepth),lo(maxdepth),hi(maxdepth), &
      trial_path(6,n),x(0:maxdepth,0:maxdepth),p(0:maxdepth),nn(0:maxdepth), &
      amat(3*maxdepth+3,maxdepth),rhs(3*maxdepth+3),sol(maxdepth),saved(maxdepth),stat=err)
    rc=3
    if (err/=0) go to 900
    rc=0
    var_for=0
    x=0_ik
    x(0,0)=int(n,ik)
    p(0)=1_ik
    nn(0)=1_ik
    call visit(0,0)
    if (arithmetic_status/=0) rc=arithmetic_status
900 continue
    do while(associated(cache))
      next_node=>cache%next
      deallocate(cache)
      cache=>next_node
    end do
    if (allocated(ids)) deallocate(ids)
    if (allocated(residues)) deallocate(residues)
    if (allocated(var_for)) deallocate(var_for)
    if (allocated(used)) deallocate(used)
    if (allocated(lo)) deallocate(lo)
    if (allocated(hi)) deallocate(hi)
    if (allocated(trial_path)) deallocate(trial_path)
    if (allocated(x)) deallocate(x)
    if (allocated(p)) deallocate(p)
    if (allocated(nn)) deallocate(nn)
    if (allocated(amat)) deallocate(amat)
    if (allocated(rhs)) deallocate(rhs)
    if (allocated(sol)) deallocate(sol)
    if (allocated(saved)) deallocate(saved)
    arithmetic_status=old_status
    if (present(status)) then
      status=rc
    else
      if (rc/=0) call fail('catalogue optimizer returned a non-answer')
    end if
  contains
    subroutine span(level,t,a,b)
      integer, intent(in) :: level,t
      integer(ik), intent(out) :: a,b
      integer :: v
      a=x(level,0)
      b=a
      do v=1,t
        a=add(a,mul(x(level,v),int(lo(v),ik)))
        b=add(b,mul(x(level,v),int(hi(v),ik)))
      end do
    end subroutine span

    recursive subroutine visit(depth,t)
      integer, intent(in) :: depth,t
      integer :: e,k,v,nt,r,i,z,zlo,zhi
      integer(ik) :: low,high,prevlo,prevhi,prefix,part,tail,scale
      logical :: fresh
      if (rc/=0 .or. arithmetic_status/=0) return
      call tick(counters(1),1_ik)
      call span(depth,t,low,high)
      if (arithmetic_status/=0) return
      zlo=int(min(int(n,ik),max(1_ik,low/p(depth))))
      if (mod(low,p(depth))/=0_ik) zlo=zlo+1
      zhi=int(min(int(n-depth,ik),high/p(depth)))
      if (zlo>zhi) return
      ! A lower bound for every assignment in this box: minimize each
      ! prefix charge separately. Never infer monotonicity of continuation.
      prefix=0_ik
      do i=1,depth
        call span(i,t,low,high)
        part=max(1_ik,low/p(i))
        if (mod(low,p(i))/=0_ik) part=part+1_ik
        prefix=sat_add(prefix,own_cost(nn(i-1),int(min(part,int(n,ik))),entries(3,ids(i))))
        call span(i-1,t,prevlo,prevhi)
        if (mul(int(entries(1,ids(i)),ik),prevhi)-low<p(i)) return
      end do
      tail=INF
      do z=zlo,zhi
        tail=min(tail,catalogue_lower(z,nn(depth)))
        if (rc/=0) return
      end do
      if (sat_add(prefix,tail)>=best_cost) then
        call tick(counters(7),1_ik)
        return
      end if
      if (depth>0) then
        do z=zlo,zhi
          if (sat_add(prefix,leaf_cost(nn(depth),z))>=best_cost) cycle
          call terminal(depth,t,z)
          if (rc/=0 .or. arithmetic_status/=0) return
        end do
      end if
      if (depth==maxdepth) return
      do e=1,size(entries,2)
        k=entries(1,e)
        if (nn(depth)>u/int(2*k-1,ik)) cycle
        v=var_for(k)
        fresh=v==0
        if (.not.fresh) then
          if (used(v)/=e) cycle
        end if
        nt=t
        if (fresh) then
          nt=t+1
          v=nt
          var_for(k)=v
          used(v)=e
          lo(v)=entries(4,e)
          hi(v)=entries(5,e)
        end if
        ids(depth+1)=e
        p(depth+1)=mul(p(depth),int(k,ik))
        nn(depth+1)=mul(nn(depth),int(2*k-1,ik))
        do r=0,k-1
          residues(depth+1)=r
          x(depth+1,:)=x(depth,:)
          scale=mul(p(depth+1),int(1+max(0,r-entries(2,e)),ik))
          x(depth+1,0)=add(x(depth,0),add(scale,-mul(p(depth),int(r,ik))))
          x(depth+1,v)=add(x(depth+1,v),p(depth+1))
          call visit(depth+1,nt)
          if (rc/=0 .or. arithmetic_status/=0) exit
        end do
        if (fresh) var_for(k)=0
        if (rc/=0 .or. arithmetic_status/=0) return
      end do
    end subroutine visit

    recursive function catalogue_lower(w,mult) result(value)
      integer, intent(in) :: w
      integer(ik), intent(in) :: mult
      integer(ik) :: value,childmult,trial
      integer :: e,k,child
      integer :: allocerr
      type(bound_node), pointer :: node
      ! Independent per-level minimum offset is a relaxation of sharing.
      ! Every larger offset gives a child in [minimum,w-1], all considered.
      value=min(u,leaf_cost(mult,w))
      if (rc/=0) return
      if (mult>u/5_ik) return
      node=>cache
      do while(associated(node))
        if (node%w==w .and. node%mult==mult) then
          value=node%value
          return
        end if
        node=>node%next
      end do
      do e=1,size(entries,2)
        k=entries(1,e)
        childmult=sat_mul(mult,int(2*k-1,ik))
        if (childmult>u/5_ik) cycle
        do child=child_width(w,k,entries(4,e),entries(4,e)-entries(2,e)),w-1
          trial=own_cost(mult,child,entries(3,e))
          if (trial>=value) exit
          trial=sat_add(trial,catalogue_lower(child,childmult))
          if (rc/=0) return
          value=min(value,trial)
        end do
      end do
      allocate(node,stat=allocerr)
      if (allocerr/=0) then
        rc=3
        return
      end if
      node%w=w
      node%mult=mult
      node%value=value
      node%prefix=INF
      node%next=>cache
      cache=>node
    end function catalogue_lower

    subroutine terminal(depth,t,z)
      integer, intent(in) :: depth,t,z
      integer :: rows,i,j,k,e,st,w,child
      integer(ik) :: objective(0:t),factor,leaf,l,h,mid,total,mult,offset
      type(ilp_stats) :: stats
      rows=0
      amat=0_ik
      rhs=0_ik
      do j=1,t
        rows=rows+1
        amat(rows,j)=1_ik
        rhs(rows)=int(hi(j),ik)
        rows=rows+1
        amat(rows,j)=-1_ik
        rhs(rows)=-int(lo(j),ik)
      end do
      do i=1,depth
        rows=rows+1
        k=entries(1,ids(i))
        do j=1,t
          amat(rows,j)=add(x(i,j),-mul(int(k,ik),x(i-1,j)))
        end do
        rhs(rows)=add(add(mul(int(k,ik),x(i-1,0)),-x(i,0)),-p(i))
      end do
      rows=rows+1
      amat(rows,1:t)=x(depth,1:t)
      rhs(rows)=add(mul(p(depth),int(z,ik)),-x(depth,0))
      rows=rows+1
      amat(rows,1:t)=-x(depth,1:t)
      rhs(rows)=-rhs(rows-1)
      objective=0_ik
      do i=1,depth
        factor=mul(mul(8_ik,nn(i-1)),int(entries(3,ids(i)),ik))
        factor=mul(factor,p(depth)/p(i))
        do j=0,t
          offset=x(i,j)
          if (j==0) offset=add(offset,-p(i))
          objective(j)=add(objective(j),mul(factor,offset))
        end do
      end do
      rows=rows+1
      amat(rows,1:t)=objective(1:t)
      leaf=leaf_cost(nn(depth),z)
      l=0_ik
      h=best_cost-1_ik
      if (leaf>h) return
      ! First establish feasibility at the current incumbent minus one.
      do
        rhs(rows)=add(mul(p(depth),h-leaf),-objective(0))
        if (arithmetic_status/=0) return
        call ilp_feasible(amat(1:rows,1:t),rhs(1:rows),sol(1:t),st,stats)
        call tick(counters(2),1_ik)
        call tick(counters(3),stats%lattice%hkz_calls)
        call tick(counters(4),stats%nodes)
        call tick(counters(5),stats%vertices)
        call tick(counters(6),stats%suffix_candidates)
        if (st>1) then
          rc=st
          return
        end if
        if (st==1) return
        saved(1:t)=sol(1:t)
        exit
      end do
      do while(l<h)
        mid=l+(h-l)/2_ik
        if (mid<leaf) then
          l=mid+1_ik
          cycle
        end if
        rhs(rows)=add(mul(p(depth),mid-leaf),-objective(0))
        if (arithmetic_status/=0) return
        call ilp_feasible(amat(1:rows,1:t),rhs(1:rows),sol(1:t),st,stats)
        call tick(counters(2),1_ik)
        call tick(counters(3),stats%lattice%hkz_calls)
        call tick(counters(4),stats%nodes)
        call tick(counters(5),stats%vertices)
        call tick(counters(6),stats%suffix_candidates)
        if (st>1) then
          rc=st
          return
        else if (st==1) then
          l=mid+1_ik
        else
          h=mid
          saved(1:t)=sol(1:t)
        end if
      end do
      w=n
      mult=1_ik
      total=0_ik
      do i=1,depth
        e=ids(i)
        k=entries(1,e)
        j=var_for(k)
        offset=saved(j)
        if (offset<int(lo(j),ik) .or. offset>int(hi(j),ik)) then
          rc=4
          return
        end if
        child=child_width(w,k,int(offset),int(offset)-entries(2,e))
        if (mod(w,k)/=residues(i) .or. child>=w .or. child<1) then
          rc=4
          return
        end if
        trial_path(:,i)=(/k,entries(3,e),int(offset),int(offset)-entries(2,e),child,e/)
        total=add(total,own_cost(mult,child,entries(3,e)))
        mult=mul(mult,int(2*k-1,ik))
        w=child
      end do
      total=add(total,leaf_cost(mult,w))
      if (arithmetic_status/=0) return
      if (w/=z .or. total/=h .or. total>=best_cost) then
        rc=4
        return
      end if
      best_cost=total
      best_depth=depth
      best_path(:,1:depth)=trial_path(:,1:depth)
    end subroutine terminal
  end subroutine optimize_catalogue
end module sp_outer
