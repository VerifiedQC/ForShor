! Derived from ../phaseproduct_f90/src/pp_oracle.f90 (byte-preserved).
! Exact charge-bounded decision: normalized prefixes never exceed C.
! Section 7 of SATURATION_AND_SINGLE_EXP_FPT.2026-10-15T190800.md.
! Exact finite-cap search in the primitive-row normal form.
! Coefficients are signed base-32768 limbs; their capacity follows the cap.
! No machine-integer coefficient truncation, helper catalogue or marker order
! restriction is used. Markers are implicit at every instruction boundary.
module sp_oracle
  implicit none
  private
  integer, parameter :: wide = selected_int_kind(18)
  integer, parameter :: limb_bits = 15, limb_base = 32768
  integer(wide), parameter :: hash_prime = 2147483629_wide
  public :: cap_decide, cap_decide_generic
  public :: cap_decide_pruned, cap_replay, replay_profile
contains
  subroutine cap_decide(k,a,b,charge_limit,status,ops,nops,states,seed_ops)
    integer, intent(in) :: k,a,b,charge_limit
    integer, intent(out) :: status,nops,states
    integer, intent(out) :: ops(:,:)
    integer, intent(in), optional :: seed_ops(:,:)
    if (present(seed_ops)) then
      call search_impl(k,a,b,charge_limit,status,ops,nops,states,.true.,.true.,.true.,.true.,seed_ops)
    else
      call search_impl(k,a,b,charge_limit,status,ops,nops,states,.true.,.true.,.true.,.true.)
    end if
  end subroutine cap_decide

  ! The same exhaustive engine without the k=2 theorem shortcut. This entry
  ! point supports independent differential tests of the state graph.
  subroutine cap_decide_generic(k,a,b,charge_limit,status,ops,nops,states,seed_ops)
    integer, intent(in) :: k,a,b,charge_limit
    integer, intent(out) :: status,nops,states
    integer, intent(out) :: ops(:,:)
    integer, intent(in), optional :: seed_ops(:,:)
    if (present(seed_ops)) then
      call search_impl(k,a,b,charge_limit,status,ops,nops,states,.false.,.false.,.false.,.false.,seed_ops)
    else
      call search_impl(k,a,b,charge_limit,status,ops,nops,states,.false.,.false.,.false.,.false.)
    end if
  end subroutine cap_decide_generic

  subroutine cap_decide_pruned(k,a,b,charge_limit,status,ops,nops,states,use_dominance,use_heuristic,seed_ops)
    integer, intent(in) :: k,a,b,charge_limit
    integer, intent(out) :: status,nops,states
    integer, intent(out) :: ops(:,:)
    logical, intent(in), optional :: use_dominance,use_heuristic
    integer, intent(in), optional :: seed_ops(:,:)
    logical :: dominance,heuristic
    dominance=.true.
    heuristic=.true.
    if (present(use_dominance)) dominance=use_dominance
    if (present(use_heuristic)) heuristic=use_heuristic
    if (present(seed_ops)) then
      call search_impl(k,a,b,charge_limit,status,ops,nops,states,.false.,.true.,dominance,heuristic,seed_ops)
    else
      call search_impl(k,a,b,charge_limit,status,ops,nops,states,.false.,.true.,dominance,heuristic)
    end if
  end subroutine cap_decide_pruned

  subroutine search_impl(k,a,b,charge_limit,status,ops,nops,states,shortcut,pruning,dominance,heuristic,seed_ops)
    integer, intent(in) :: k,a,b,charge_limit
    integer, intent(out) :: status,nops,states
    integer, intent(out) :: ops(:,:)
    logical, intent(in) :: shortcut,pruning,dominance,heuristic
    integer, intent(in), optional :: seed_ops(:,:)
    integer, allocatable :: mat(:,:,:,:), u0(:,:), ur(:,:), target(:,:,:)
    integer, allocatable :: distance(:), parent(:), move(:,:), bucket(:), link(:)
    integer, allocatable :: heap(:), position(:), candidate(:,:,:), v0(:), vr(:)
    integer, allocatable :: shifted_d(:), shifted_h(:), total(:)
    integer, allocatable :: estimate(:)
    integer(wide), allocatable :: hashes(:)
    logical, allocatable :: covered(:,:), seen(:),active(:)
    integer :: c,nl,nt,rcap,nb,err,hs,cur,d,h,s,e,side,p,q,t,j,i,sg,ex,capacity
    integer :: edge(7), charge, candidate_cost, candidate_estimate, slot, node, incumbent
    integer :: last, required, pos, kind, step, minexp
    integer(wide) :: z0,zr,exwide,slotswide,cells,needed,hashvalue
    logical :: halted,identity,overflow

    status=3
    c=-1
    nops=0
    states=0
    ops=0
    if (k<2 .or. a<0 .or. b<0 .or. charge_limit<0) return
    if (size(ops,1)/=5) return
    if (b>a) return
    if (int(b,wide)<max(0_wide,int(a,wide)-int(k,wide)+1_wide)) return
    if (int(b,wide)+int(k,wide)-1_wide>int(huge(rcap),wide)) then
      status=2
      return
    end if
    rcap=int(int(b,wide)+int(k,wide)-1_wide)
    incumbent=-1
    ! A caller-supplied word is never trusted, even on the k=2 shortcut.
    ! Literal replay includes transient scanner peaks before any division.
    if (present(seed_ops)) then
      call verify_seed(k,a,rcap,seed_ops,status,incumbent)
      if (status/=0) return
      if (incumbent<=charge_limit) then
        status=2
        if (size(seed_ops,2)>size(ops,2)) return
        ops(:,1:size(seed_ops,2))=seed_ops
        nops=size(seed_ops,2)
        status=0
        return
      end if
    end if
    if (shortcut .and. k==2) then
      status=1
      if (b<2 .or. charge_limit<4) return
      status=2
      if (size(ops,2)<2) return
      ops(:,1)=(/1,1,2,-1,0/)
      ops(:,2)=(/1,1,2,1,0/)
      c=4
      nops=2
      status=0
      return
    end if
    status=2
    if (int(k,wide)*2_wide-1_wide>int(huge(nt),wide)) return
    nt=int(2_wide*int(k,wide)-1_wide)
    ! Every target must fit the zero-seed row-mass bound. The largest
    ! coordinate exponent alone is a cheap necessary test, computed wide.
    if (nt>=5) then
      exwide=int((nt-5)/4+1,wide)*int(k-1,wide)
      if (exwide>int(a,wide)) then
        status=1
        return
      end if
    end if
    nl=a/limb_bits+2
    ! Storage grows without a resource cutoff; C bounds mathematical word charge.
    capacity=256
    slotswide=2_wide*int(capacity,wide)+1_wide
    if (slotswide>int(huge(nb),wide)) return
    nb=max(17,int(slotswide))
    ! Guard shape arithmetic before allocation; allocation itself has STAT.
    cells=int(nl,wide)
    if (.not. multiply_shape(cells,k)) return
    if (.not. multiply_shape(cells,k)) return
    if (.not. multiply_shape(cells,capacity)) return
    if (.not. multiply_shape(cells,4)) return
    allocate(mat(nl,k,k,capacity),u0(k,capacity),ur(k,capacity), &
      target(nl,k,nt),distance(capacity),parent(capacity), &
      move(7,capacity),bucket(nb),link(capacity),heap(capacity), &
      position(capacity),hashes(capacity),candidate(nl,k,k),v0(k),vr(k), &
      covered(nt,capacity),seen(nt),active(capacity),estimate(capacity),shifted_d(nl),shifted_h(nl), &
      total(nl),stat=err)
    if (err/=0) then
      status=3
      go to 9000
    end if
    target=0
    target(1,1,1)=1
    target(1,k,2)=1
    do i=3,nt
      do j=1,k
        if (i<=4) then
          ex=0
          step=j-1
        else
          e=(i-5)/4+1
          if (mod(i-5,4)<2) then
            step=k-j
          else
            step=j-1
          end if
          ex=e*step
        end if
        sg=1
        if (mod(i,2)==1 .and. mod(step,2)==1) sg=-1
        target(ex/limb_bits+1,j,i)=sg*2**mod(ex,limb_bits)
      end do
    end do
    bucket=0
    hs=0
    states=1
    mat(:,:,:,1)=0
    do i=1,k
      mat(1,i,i,1)=1
    end do
    u0(:,1)=0
    ur(:,1)=0
    ur(k,1)=k-1
    covered(:,1)=.false.
    candidate=mat(:,:,:,1)
    seen=covered(:,1)
    call mark_targets()
    covered(:,1)=seen
    v0=u0(:,1)
    vr=ur(:,1)
    slot=state_slot()
    hashes(1)=hashvalue
    bucket(slot)=1
    link(1)=0
    distance(1)=0
    estimate(1)=remaining_charge()
    active(1)=.true.
    parent(1)=0
    move(:,1)=0
    if (estimate(1)<=charge_limit) call heap_push(1)
    halted=.false.
    status=1
    do while(hs>0)
      call heap_pop(cur)
      if (.not.active(cur)) cycle
      identity=.true.
      if (all(covered(:,cur))) then
        do d=1,k
          do j=1,k
            if (d==j) then
              if (mat(1,j,d,cur)/=1) identity=.false.
            else
              if (mat(1,j,d,cur)/=0) identity=.false.
            end if
            if (any(mat(2:nl,j,d,cur)/=0)) identity=.false.
          end do
        end do
        if (identity) then
          call reconstruct(cur)
          go to 9000
        end if
      end if
      do d=1,k
        if (distance(cur)<charge_limit .and. u0(d,cur)<a .and. ur(d,cur)<rcap) then
          candidate=mat(:,:,:,cur)
          candidate(:,:,d)=-candidate(:,:,d)
          v0=u0(:,cur)
          vr=ur(:,cur)
          v0(d)=v0(d)+1
          vr(d)=vr(d)+1
          seen=covered(:,cur)
          edge=(/4,d,0,0,0,0,0/)
          call relax(1)
          if (halted) go to 9000
        end if
        do h=1,k
          if (d==h) cycle
          do side=1,2
            minexp=0
            if (side==2) minexp=1
            do e=minexp,a-1
              p=0
              q=e
              if (side==2) then
                p=e
                q=0
              end if
              z0=1_wide+max(int(u0(d,cur),wide)+int(p,wide), &
                int(u0(h,cur),wide)+int(q,wide))
              zr=1_wide+max(int(ur(d,cur),wide)+int(p,wide), &
                int(ur(h,cur),wide)+int(q,wide))
              ! Test the transient addition BEFORE normalization.
              if (z0>int(a,wide) .or. zr>int(rcap,wide)) cycle
              do s=1,-1,-2
                charge=1
                if (s<0) charge=3
                if (distance(cur)>charge_limit-charge) cycle
                candidate=mat(:,:,:,cur)
                t=a
                do j=1,k
                  call limb_shift_left(mat(:,j,d,cur),p,shifted_d,overflow)
                  if (overflow) then
                    status=2
                    go to 9000
                  end if
                  call limb_shift_left(mat(:,j,h,cur),q,shifted_h,overflow)
                  if (overflow) then
                    status=2
                    go to 9000
                  end if
                  shifted_h=s*shifted_h
                  call limb_add(shifted_d,shifted_h,total,overflow)
                  if (overflow) then
                    status=2
                    go to 9000
                  end if
                  candidate(:,j,d)=total
                  t=min(t,limb_valuation(total))
                end do
                ! Invertibility rules out a zero row. Negative scanner
                ! values would violate the exact integral mass invariant.
                if (t>int(z0) .or. t>int(zr)) then
                  status=3
                  go to 9000
                end if
                do j=1,k
                  call limb_shift_right(candidate(:,j,d),t,total)
                  candidate(:,j,d)=total
                end do
                v0=u0(:,cur)
                vr=ur(:,cur)
                v0(d)=int(z0)-t
                vr(d)=int(zr)-t
                seen=covered(:,cur)
                edge=(/1,d,h,s,p,q,t/)
                charge=1
                if (s<0) charge=3
                call relax(charge)
                if (halted) go to 9000
              end do
            end do
          end do
        end do
      end do
    end do
    ! Every retained prefix has charge <= C. Exhaustion is an exact NO.
    status=1
9000 continue
    ! F90 does not guarantee automatic deallocation of unsaved local
    ! allocatables. Guard each object because STAT failure may be partial.
    if (allocated(mat)) deallocate(mat)
    if (allocated(u0)) deallocate(u0)
    if (allocated(ur)) deallocate(ur)
    if (allocated(target)) deallocate(target)
    if (allocated(distance)) deallocate(distance)
    if (allocated(parent)) deallocate(parent)
    if (allocated(move)) deallocate(move)
    if (allocated(bucket)) deallocate(bucket)
    if (allocated(link)) deallocate(link)
    if (allocated(heap)) deallocate(heap)
    if (allocated(position)) deallocate(position)
    if (allocated(candidate)) deallocate(candidate)
    if (allocated(v0)) deallocate(v0)
    if (allocated(vr)) deallocate(vr)
    if (allocated(shifted_d)) deallocate(shifted_d)
    if (allocated(shifted_h)) deallocate(shifted_h)
    if (allocated(total)) deallocate(total)
    if (allocated(hashes)) deallocate(hashes)
    if (allocated(covered)) deallocate(covered)
    if (allocated(seen)) deallocate(seen)
    if (allocated(active)) deallocate(active)
    if (allocated(estimate)) deallocate(estimate)
    return
  contains
    subroutine mark_targets()
      integer :: it,ir
      do it=1,nt
        if (seen(it)) cycle
        do ir=1,k
          if (all(candidate(:,:,ir)==target(:,:,it))) then
            seen(it)=.true.
            exit
          end if
        end do
      end do
    end subroutine mark_targets

    integer function state_slot()
      integer :: ir,ic,il,it
      hashvalue=1_wide
      do ir=1,k
        do ic=1,k
          do il=1,nl
            hashvalue=mod(hashvalue*65599_wide+ &
              int(candidate(il,ic,ir)+limb_base,wide),hash_prime)
          end do
        end do
        if (.not.dominance) then
          hashvalue=mod(hashvalue*65599_wide+int(v0(ir),wide),hash_prime)
          hashvalue=mod(hashvalue*65599_wide+int(vr(ir),wide),hash_prime)
        end if
      end do
      if (.not.dominance) then
        do it=1,nt
          hashvalue=mod(hashvalue*2_wide,hash_prime)
          if (seen(it)) hashvalue=hashvalue+1_wide
        end do
      end if
      state_slot=int(mod(hashvalue,int(nb,wide)))+1
    end function state_slot

    logical function dead_row()
      integer :: ir,ic
      logical :: basis
      dead_row=.false.
      do ir=1,k
        if (v0(ir)<a .and. vr(ir)<rcap) cycle
        basis=.true.
        do ic=1,k
          if (ic==ir) then
            if (candidate(1,ic,ir)/=1) basis=.false.
          else
            if (candidate(1,ic,ir)/=0) basis=.false.
          end if
          if (any(candidate(2:nl,ic,ir)/=0)) basis=.false.
        end do
        if (.not.basis) then
          dead_row=.true.
          return
        end if
      end do
    end function dead_row

    integer function remaining_charge()
      integer :: ir,ic
      logical :: basis
      remaining_charge=0
      if (.not.heuristic) return
      ! Unseen nonbasis targets require distinct future target-producing
      ! macros. Each currently wrong row also needs a final basis-producing
      ! macro; these cannot be the same event. h drops by at most one per
      ! charged macro, so h is consistent as well as admissible.
      remaining_charge=count(.not.seen)
      do ir=1,k
        basis=.true.
        do ic=1,k
          if (ic==ir) then
            if (candidate(1,ic,ir)/=1) basis=.false.
          else
            if (candidate(1,ic,ir)/=0) basis=.false.
          end if
          if (any(candidate(2:nl,ic,ir)/=0)) basis=.false.
        end do
        if (.not.basis) remaining_charge=remaining_charge+1
      end do
    end function remaining_charge

    subroutine relax(cost)
      integer, intent(in) :: cost
      ! A primitive nonidentity row must eventually receive a charged write.
      ! Such a write raises its transient scanner by at least one.
      if (pruning) then
        if (dead_row()) return
      end if
      call mark_targets()
      if (distance(cur)>huge(candidate_cost)-cost) then
        status=2
        halted=.true.
        return
      end if
      candidate_cost=distance(cur)+cost
      candidate_estimate=remaining_charge()
      ! Admissible remaining charge cannot remove a feasible <=C suffix.
      if (int(candidate_cost,wide)+int(candidate_estimate,wide)>int(charge_limit,wide)) return
      slot=state_slot()
      node=bucket(slot)
      do while(node/=0)
        if (active(node) .and. hashes(node)==hashvalue) then
          if (all(candidate==mat(:,:,:,node))) then
            if (all(v0==u0(:,node)) .and. all(vr==ur(:,node))) then
              if (all(seen .eqv. covered(:,node))) exit
            end if
            if (dominance) then
              if (distance(node)<=candidate_cost) then
                if (all(u0(:,node)<=v0) .and. all(ur(:,node)<=vr)) then
                  if (all(covered(:,node) .or. .not.seen)) return
                end if
              end if
              if (candidate_cost<=distance(node)) then
                if (all(v0<=u0(:,node)) .and. all(vr<=ur(:,node))) then
                  ! Keep predecessor storage intact; skip retired labels
                  ! when popped. Every retained suffix remains replayable.
                  if (all(seen .or. .not.covered(:,node))) active(node)=.false.
                end if
              end if
            end if
          end if
        end if
        node=link(node)
      end do
      if (node==0) then
        if (states==capacity) then
          call grow_storage()
          if (halted) return
          slot=int(mod(hashvalue,int(nb,wide)))+1
        end if
        states=states+1
        node=states
        mat(:,:,:,node)=candidate
        u0(:,node)=v0
        ur(:,node)=vr
        covered(:,node)=seen
        active(node)=.true.
        estimate(node)=candidate_estimate
        distance(node)=candidate_cost
        parent(node)=cur
        move(:,node)=edge
        hashes(node)=hashvalue
        link(node)=bucket(slot)
        bucket(slot)=node
        call heap_push(node)
      else if (candidate_cost<distance(node)) then
        if (position(node)==0) then
          status=3
          halted=.true.
          return
        end if
        distance(node)=candidate_cost
        parent(node)=cur
        move(:,node)=edge
        call heap_up(position(node))
      end if
    end subroutine relax

    subroutine grow_storage()
      integer, allocatable :: gm(:,:,:,:),g0(:,:),gr(:,:),gd(:),gp(:),ge(:,:)
      integer, allocatable :: gh(:),gpos(:),gest(:)
      integer(wide), allocatable :: ghash(:)
      logical, allocatable :: gc(:,:),ga(:)
      integer :: nextcap,nextnb,ii,ss,allocation_status
      integer(wide) :: nextwide,shape
      ! F90 has no move_alloc; retain the old arrays in temporary storage,
      ! then allocate the new state arrays and copy the live prefix back.
      nextwide=2_wide*int(capacity,wide)
      if (2_wide*nextwide+1_wide>int(huge(nextcap),wide)) then
        status=2
        halted=.true.
        return
      end if
      nextcap=int(nextwide)
      nextnb=max(17,2*nextcap+1)
      shape=int(nl,wide)
      if (.not. multiply_shape(shape,k)) then
        status=3
        halted=.true.
        return
      end if
      if (.not. multiply_shape(shape,k)) then
        status=3
        halted=.true.
        return
      end if
      if (.not. multiply_shape(shape,nextcap)) then
        status=3
        halted=.true.
        return
      end if
      if (.not. multiply_shape(shape,4)) then
        status=3
        halted=.true.
        return
      end if
      allocate(gm(nl,k,k,states),g0(k,states),gr(k,states),gd(states), &
        gp(states),ge(7,states),gh(hs),gpos(states),ghash(states), &
        ga(states),gest(states),gc(nt,states),stat=allocation_status)
      if (allocation_status/=0) then
        status=3
        halted=.true.
        go to 9000
      end if
      gm=mat(:,:,:,1:states)
      g0=u0(:,1:states)
      gr=ur(:,1:states)
      gd=distance(1:states)
      gp=parent(1:states)
      ge=move(:,1:states)
      gh=heap(1:hs)
      gpos=position(1:states)
      ghash=hashes(1:states)
      gc=covered(:,1:states)
      ga=active(1:states)
      gest=estimate(1:states)
      deallocate(mat,u0,ur,distance,parent,move,heap,position,hashes,covered,active,estimate,bucket,link)
      allocate(mat(nl,k,k,nextcap),u0(k,nextcap),ur(k,nextcap), &
        distance(nextcap),parent(nextcap),move(7,nextcap),heap(nextcap), &
        position(nextcap),hashes(nextcap),covered(nt,nextcap),active(nextcap),estimate(nextcap), &
        bucket(nextnb),link(nextcap),stat=allocation_status)
      if (allocation_status/=0) then
        status=3
        halted=.true.
        go to 9000
      end if
      mat(:,:,:,1:states)=gm
      u0(:,1:states)=g0
      ur(:,1:states)=gr
      distance(1:states)=gd
      parent(1:states)=gp
      move(:,1:states)=ge
      heap(1:hs)=gh
      position(1:states)=gpos
      hashes(1:states)=ghash
      covered(:,1:states)=gc
      active(1:states)=ga
      estimate(1:states)=gest
      bucket=0
      do ii=1,states
        ss=int(mod(hashes(ii),int(nextnb,wide)))+1
        link(ii)=bucket(ss)
        bucket(ss)=ii
      end do
      capacity=nextcap
      nb=nextnb
9000  continue
      if (allocated(gm)) deallocate(gm)
      if (allocated(g0)) deallocate(g0)
      if (allocated(gr)) deallocate(gr)
      if (allocated(gd)) deallocate(gd)
      if (allocated(gp)) deallocate(gp)
      if (allocated(ge)) deallocate(ge)
      if (allocated(gh)) deallocate(gh)
      if (allocated(gpos)) deallocate(gpos)
      if (allocated(ghash)) deallocate(ghash)
      if (allocated(gc)) deallocate(gc)
      if (allocated(ga)) deallocate(ga)
      if (allocated(gest)) deallocate(gest)
      return
    end subroutine grow_storage

    logical function precedes(x,y)
      integer, intent(in) :: x,y
      integer(wide) :: fx,fy
      fx=int(distance(x),wide)+int(estimate(x),wide)
      fy=int(distance(y),wide)+int(estimate(y),wide)
      precedes=fx<fy
      if (fx==fy) then
        precedes=distance(x)>distance(y)
        if (distance(x)==distance(y)) precedes=x<y
      end if
    end function precedes

    subroutine heap_push(x)
      integer, intent(in) :: x
      hs=hs+1
      heap(hs)=x
      position(x)=hs
      call heap_up(hs)
    end subroutine heap_push

    subroutine heap_up(start)
      integer, intent(in) :: start
      integer :: at,above,hold
      at=start
      do while(at>1)
        above=at/2
        if (.not. precedes(heap(at),heap(above))) exit
        hold=heap(above)
        heap(above)=heap(at)
        heap(at)=hold
        position(heap(at))=at
        position(heap(above))=above
        at=above
      end do
    end subroutine heap_up

    subroutine heap_pop(x)
      integer, intent(out) :: x
      integer :: at,left,right,best,hold
      x=heap(1)
      position(x)=0
      if (hs==1) then
        hs=0
        return
      end if
      heap(1)=heap(hs)
      hs=hs-1
      position(heap(1))=1
      at=1
      do while(at<=hs/2)
        left=2*at
        right=left+1
        best=left
        if (right<=hs) then
          if (precedes(heap(right),heap(left))) best=right
        end if
        if (.not. precedes(heap(best),heap(at))) exit
        hold=heap(at)
        heap(at)=heap(best)
        heap(best)=hold
        position(heap(at))=at
        position(heap(best))=best
        at=best
      end do
    end subroutine heap_pop

    subroutine reconstruct(goal)
      integer, intent(in) :: goal
      last=goal
      needed=0_wide
      do while(parent(last)/=0)
        needed=needed+1_wide
        if (move(1,last)==1) then
          if (move(5,last)>0) needed=needed+1_wide
          if (move(7,last)>0) needed=needed+1_wide
        end if
        last=parent(last)
      end do
      status=2
      if (needed>int(size(ops,2),wide)) return
      required=int(needed)
      pos=required
      last=goal
      do while(parent(last)/=0)
        kind=move(1,last)
        d=move(2,last)
        if (kind==4) then
          ops(:,pos)=(/4,d,0,0,0/)
          pos=pos-1
        else
          if (move(7,last)>0) then
            ops(:,pos)=(/3,d,0,0,move(7,last)/)
            pos=pos-1
          end if
          ops(:,pos)=(/1,d,move(3,last),move(4,last),move(6,last)/)
          pos=pos-1
          if (move(5,last)>0) then
            ops(:,pos)=(/2,d,0,0,move(5,last)/)
            pos=pos-1
          end if
        end if
        last=parent(last)
      end do
      c=distance(goal)
      nops=required
      status=0
    end subroutine reconstruct
  end subroutine search_impl

  subroutine cap_replay(k,a,b,ops,status,charge)
    integer, intent(in) :: k,a,b,ops(:,:)
    integer, intent(out) :: status,charge
    integer(wide) :: r
    status=3
    charge=-1
    if (k<2 .or. a<0 .or. b<0) return
    r=int(b,wide)+int(k,wide)-1_wide
    status=2
    if (r>int(huge(a),wide)) return
    call verify_seed(k,a,int(r),ops,status,charge)
  end subroutine cap_replay

  subroutine replay_profile(k,ops,status,charge,a0,b0)
    integer, intent(in) :: k,ops(:,:)
    integer, intent(out) :: status,charge,a0,b0
    integer(wide) :: bound
    integer :: peakr
    status=3
    charge=-1
    a0=-1
    b0=-1
    if (k<2) return
    bound=int(k,wide)*int(k,wide)
    status=2
    if (bound>int(huge(a0)-k+1,wide)/8_wide) return
    bound=8_wide*bound
    if (bound+int(k,wide)-1_wide>int(huge(a0),wide)) return
    call verify_seed(k,int(bound),int(bound)+k-1,ops,status,charge,a0,peakr)
    if (status==0) b0=peakr-(k-1)
  end subroutine replay_profile

  subroutine verify_seed(k,a,rcap,seed_ops,status,charge,peak0,peakr)
    integer, intent(in) :: k,a,rcap,seed_ops(:,:)
    integer, intent(out) :: status,charge
    integer, intent(out), optional :: peak0,peakr
    integer, allocatable :: matrix(:,:,:),targets(:,:,:),scan0(:),scanr(:)
    integer, allocatable :: shifted(:),total(:)
    logical, allocatable :: visited(:)
    integer :: nl,nt,err,i,j,t,ir,kind,d,h,sg,shift,e,step,ex,cost
    integer(wide) :: shape,new0,newr,exwide
    logical :: overflow,identity
    status=3
    charge=-1
    if (size(seed_ops,1)/=5) return
    if (int(k,wide)*2_wide-1_wide>int(huge(nt),wide)) then
      status=2
      return
    end if
    nt=int(2_wide*int(k,wide)-1_wide)
    if (nt>=5) then
      exwide=int((nt-5)/4+1,wide)*int(k-1,wide)
      if (exwide>int(a,wide)) return
    end if
    nl=a/limb_bits+2
    shape=int(nl,wide)
    status=2
    if (.not.multiply_shape(shape,k)) return
    if (.not.multiply_shape(shape,nt)) return
    if (.not.multiply_shape(shape,4)) return
    allocate(matrix(nl,k,k),targets(nl,k,nt),scan0(k),scanr(k), &
      shifted(nl),total(nl),visited(nt),stat=err)
    if (err/=0) then
      status=3
      go to 9000
    end if
    status=3
    matrix=0
    do i=1,k
      matrix(1,i,i)=1
    end do
    targets=0
    targets(1,1,1)=1
    targets(1,k,2)=1
    do i=3,nt
      do j=1,k
        if (i<=4) then
          ex=0
          step=j-1
        else
          e=(i-5)/4+1
          if (mod(i-5,4)<2) then
            step=k-j
          else
            step=j-1
          end if
          ex=e*step
        end if
        sg=1
        if (mod(i,2)==1 .and. mod(step,2)==1) sg=-1
        targets(ex/limb_bits+1,j,i)=sg*2**mod(ex,limb_bits)
      end do
    end do
    visited=.false.
    call mark_seed_targets()
    scan0=0
    scanr=0
    scanr(k)=k-1
    if (present(peak0)) peak0=0
    if (present(peakr)) peakr=k-1
    cost=0
    do i=1,size(seed_ops,2)
      kind=seed_ops(1,i)
      d=seed_ops(2,i)
      h=seed_ops(3,i)
      sg=seed_ops(4,i)
      shift=seed_ops(5,i)
      if (d<1 .or. d>k .or. shift<0) go to 9000
      if (kind==1) then
        if (h<1 .or. h>k .or. h==d) go to 9000
        if (sg/=-1 .and. sg/=1) go to 9000
        new0=1_wide+max(int(scan0(d),wide),int(scan0(h),wide)+int(shift,wide))
        newr=1_wide+max(int(scanr(d),wide),int(scanr(h),wide)+int(shift,wide))
      else
        ! Unused fields are canonical zero, not arbitrary ignored input.
        if (h/=0 .or. sg/=0) go to 9000
        if (kind==2) then
          new0=int(scan0(d),wide)+int(shift,wide)
          newr=int(scanr(d),wide)+int(shift,wide)
        else if (kind==3) then
          new0=int(scan0(d),wide)-int(shift,wide)
          newr=int(scanr(d),wide)-int(shift,wide)
        else if (kind==4) then
          if (shift/=0) go to 9000
          new0=int(scan0(d),wide)+1_wide
          newr=int(scanr(d),wide)+1_wide
        else
          go to 9000
        end if
      end if
      ! Check both complete histories one boundary at a time; later free
      ! divisions cannot erase an earlier peak or permit a negative scan.
      if (new0<0_wide .or. newr<0_wide) go to 9000
      if (new0>int(a,wide) .or. newr>int(rcap,wide)) go to 9000
      do j=1,k
        if (kind==1) then
          call limb_shift_left(matrix(:,j,h),shift,shifted,overflow)
          if (overflow) go to 9000
          shifted=sg*shifted
          call limb_add(matrix(:,j,d),shifted,total,overflow)
          if (overflow) go to 9000
          matrix(:,j,d)=total
        else if (kind==2) then
          call limb_shift_left(matrix(:,j,d),shift,total,overflow)
          if (overflow) go to 9000
          matrix(:,j,d)=total
        else if (kind==3) then
          if (limb_valuation(matrix(:,j,d))<shift) go to 9000
          call limb_shift_right(matrix(:,j,d),shift,total)
          matrix(:,j,d)=total
        else
          matrix(:,j,d)=-matrix(:,j,d)
        end if
      end do
      scan0(d)=int(new0)
      scanr(d)=int(newr)
      if (present(peak0)) peak0=max(peak0,int(new0))
      if (present(peakr)) peakr=max(peakr,int(newr))
      t=0
      if (kind==1) then
        t=1
        if (sg<0) t=3
      else if (kind==4) then
        t=1
      end if
      if (cost>huge(cost)-t) then
        status=2
        go to 9000
      end if
      cost=cost+t
      call mark_seed_targets()
    end do
    if (.not.all(visited)) go to 9000
    identity=.true.
    do ir=1,k
      do j=1,k
        t=0
        if (ir==j) t=1
        if (matrix(1,j,ir)/=t .or. any(matrix(2:nl,j,ir)/=0)) identity=.false.
      end do
    end do
    if (.not.identity) go to 9000
    charge=cost
    status=0
9000 continue
    if (allocated(matrix)) deallocate(matrix)
    if (allocated(targets)) deallocate(targets)
    if (allocated(scan0)) deallocate(scan0)
    if (allocated(scanr)) deallocate(scanr)
    if (allocated(shifted)) deallocate(shifted)
    if (allocated(total)) deallocate(total)
    if (allocated(visited)) deallocate(visited)
    return
  contains
    subroutine mark_seed_targets()
      integer :: it,row
      do it=1,nt
        if (visited(it)) cycle
        do row=1,k
          if (all(matrix(:,:,row)==targets(:,:,it))) then
            visited(it)=.true.
            exit
          end if
        end do
      end do
    end subroutine mark_seed_targets
  end subroutine verify_seed

  logical function multiply_shape(value,factor)
    integer(wide), intent(inout) :: value
    integer, intent(in) :: factor
    multiply_shape=.false.
    if (factor<0) return
    if (factor==0) then
      value=0_wide
    else
      if (value>huge(value)/int(factor,wide)) return
      value=value*int(factor,wide)
    end if
    multiply_shape=.true.
  end function multiply_shape

  integer function limb_sign(x)
    integer, intent(in) :: x(:)
    integer :: i
    limb_sign=0
    do i=size(x),1,-1
      if (x(i)>0) then
        limb_sign=1
        return
      else if (x(i)<0) then
        limb_sign=-1
        return
      end if
    end do
  end function limb_sign

  subroutine limb_shift_left(x,shift,y,overflow)
    integer, intent(in) :: x(:),shift
    integer, intent(out) :: y(:)
    logical, intent(out) :: overflow
    integer :: offset,bits,i,to,sg
    integer(wide) :: carry,value,factor
    y=0
    overflow=.false.
    offset=shift/limb_bits
    bits=mod(shift,limb_bits)
    factor=2_wide**bits
    sg=limb_sign(x)
    carry=0_wide
    do i=1,size(x)
      value=int(abs(x(i)),wide)*factor+carry
      carry=value/int(limb_base,wide)
      to=i+offset
      if (to<=size(y)) then
        y(to)=sg*int(mod(value,int(limb_base,wide)))
      else if (value/=0_wide) then
        overflow=.true.
      end if
    end do
    if (carry/=0_wide) overflow=.true.
  end subroutine limb_shift_left

  subroutine limb_shift_right(x,shift,y)
    integer, intent(in) :: x(:),shift
    integer, intent(out) :: y(:)
    integer :: offset,bits,i,from,sg
    integer(wide) :: value,divisor
    y=0
    offset=shift/limb_bits
    bits=mod(shift,limb_bits)
    divisor=2_wide**bits
    sg=limb_sign(x)
    do i=1,size(y)
      from=i+offset
      if (from>size(x)) exit
      value=int(abs(x(from)),wide)
      if (from<size(x)) value=value+int(abs(x(from+1)),wide)*int(limb_base,wide)
      y(i)=sg*int(mod(value/divisor,int(limb_base,wide)))
    end do
  end subroutine limb_shift_right

  subroutine limb_add(x,y,z,overflow)
    integer, intent(in) :: x(:),y(:)
    integer, intent(out) :: z(:)
    logical, intent(out) :: overflow
    integer :: sx,sy,cmp,i,sg
    integer(wide) :: carry,value
    sx=limb_sign(x)
    sy=limb_sign(y)
    z=0
    overflow=.false.
    if (sx==0) then
      z=y
      return
    else if (sy==0) then
      z=x
      return
    end if
    carry=0_wide
    if (sx==sy) then
      do i=1,size(z)
        value=int(abs(x(i)),wide)+int(abs(y(i)),wide)+carry
        z(i)=sx*int(mod(value,int(limb_base,wide)))
        carry=value/int(limb_base,wide)
      end do
      overflow=carry/=0_wide
      return
    end if
    cmp=0
    do i=size(z),1,-1
      if (abs(x(i))>abs(y(i))) then
        cmp=1
        exit
      else if (abs(x(i))<abs(y(i))) then
        cmp=-1
        exit
      end if
    end do
    if (cmp==0) return
    sg=sx
    if (cmp<0) sg=sy
    do i=1,size(z)
      value=int(cmp,wide)*(int(abs(x(i)),wide)-int(abs(y(i)),wide))-carry
      carry=0_wide
      if (value<0_wide) then
        value=value+int(limb_base,wide)
        carry=1_wide
      end if
      z(i)=sg*int(value)
    end do
  end subroutine limb_add

  integer function limb_valuation(x)
    integer, intent(in) :: x(:)
    integer :: i,digit
    limb_valuation=huge(limb_valuation)
    do i=1,size(x)
      if (x(i)/=0) then
        digit=abs(x(i))
        limb_valuation=(i-1)*limb_bits
        do while(mod(digit,2)==0)
          digit=digit/2
          limb_valuation=limb_valuation+1
        end do
        return
      end if
    end do
  end function limb_valuation
end module sp_oracle
