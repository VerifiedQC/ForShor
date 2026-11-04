! Immutable arbitrary-precision rational handles. All storage belongs to one arena.
! Base 10^6 limbs; each individual limb product/carry fits selected_int_kind(18).
module sp_rational
  use sp_arithmetic, only: ik
  implicit none
  private
  integer(ik), parameter :: base=1000000_ik
  type big
    integer :: sign
    integer(ik), pointer :: d(:)
  end type big
  type rational
    type(big) :: n,q
  end type rational
  type(rational), pointer :: arena(:)
  logical :: arena_live=.false.
  integer :: used=0,capacity=0
  integer :: allocation_count=0
  integer, public :: r_fail_after=-1
  integer, public :: r0=1,r1=2,r_status=0
  public :: r_start,r_finish,ri,ra,rs,rm,rd,rn,rc,rz,rzint,rf,rroot,rtoi,rnum,rden
contains
  function may_allocate() result(ok)
    logical :: ok
    ok=.false.
    if(r_status/=0) return
    if(r_fail_after>=0.and.allocation_count>=r_fail_after) then
      r_status=3; return
    end if
    allocation_count=allocation_count+1
    ok=.true.
  end function may_allocate

  subroutine bz(a)
    type(big), intent(inout) :: a
    if(associated(a%d)) deallocate(a%d)
    nullify(a%d); a%sign=0
  end subroutine bz

  subroutine bn(a,n)
    type(big), intent(out) :: a
    integer, intent(in) :: n
    integer :: st
    nullify(a%d); a%sign=0
    if(.not.may_allocate()) return
    allocate(a%d(max(1,n)),stat=st)
    if(st/=0) then
      r_status=3; return
    end if
    a%d=0_ik; a%sign=0
  end subroutine bn

  subroutine trim(a)
    type(big), intent(inout) :: a
    integer(ik), pointer :: p(:)
    integer :: n,st
    if(r_status/=0) return
    n=size(a%d)
    do while(n>1)
      if(a%d(n)/=0_ik) exit
      n=n-1
    end do
    if(n<size(a%d)) then
      if(.not.may_allocate()) return
      allocate(p(n),stat=st)
      if(st/=0) then
        r_status=3; return
      end if
      p=a%d(1:n); deallocate(a%d); a%d=>p
    end if
    if(n==1.and.a%d(1)==0_ik) a%sign=0
  end subroutine trim

  subroutine bc(a,b)
    type(big), intent(in) :: a
    type(big), intent(out) :: b
    nullify(b%d); b%sign=0
    if(r_status/=0) return
    call bn(b,size(a%d))
    if(r_status/=0) return
    b%d=a%d; b%sign=a%sign
  end subroutine bc

  subroutine bi(v,a)
    integer(ik), intent(in) :: v
    type(big), intent(out) :: a
    integer(ik) :: w,part
    integer :: n,j
    ! Work in nonpositive values, permitting the most-negative native integer.
    w=v
    if(w>0_ik) w=-w
    n=1; part=w
    do while(part<=-base)
      n=n+1; part=part/base
    end do
    call bn(a,n)
    if(r_status/=0) return
    do j=1,n
      a%d(j)=-mod(w,base); w=w/base
    end do
    if(v>0_ik) a%sign=1
    if(v<0_ik) a%sign=-1
  end subroutine bi

  function cmpabs(a,b) result(c)
    type(big), intent(in) :: a,b
    integer :: c,i
    c=0
    if(size(a%d)>size(b%d)) then
      c=1; return
    else if(size(a%d)<size(b%d)) then
      c=-1; return
    end if
    do i=size(a%d),1,-1
      if(a%d(i)>b%d(i)) then
        c=1; return
      else if(a%d(i)<b%d(i)) then
        c=-1; return
      end if
    end do
  end function cmpabs

  subroutine addabs(a,b,c)
    type(big), intent(in) :: a,b
    type(big), intent(out) :: c
    integer :: i,n
    integer(ik) :: s,carry
    nullify(c%d); c%sign=0
    if(r_status/=0) return
    n=max(size(a%d),size(b%d)); call bn(c,n+1); carry=0_ik
    if(r_status/=0) return
    do i=1,n
      s=carry
      if(i<=size(a%d)) s=s+a%d(i)
      if(i<=size(b%d)) s=s+b%d(i)
      c%d(i)=mod(s,base); carry=s/base
    end do
    c%d(n+1)=carry; c%sign=1; call trim(c)
  end subroutine addabs

  subroutine subabs(a,b,c)
    type(big), intent(in) :: a,b
    type(big), intent(out) :: c
    integer :: i
    integer(ik) :: v,borrow
    nullify(c%d); c%sign=0
    if(r_status/=0) return
    call bn(c,size(a%d)); borrow=0_ik
    if(r_status/=0) return
    do i=1,size(a%d)
      v=a%d(i)-borrow
      if(i<=size(b%d)) v=v-b%d(i)
      borrow=0_ik
      if(v<0_ik) then
        v=v+base; borrow=1_ik
      end if
      c%d(i)=v
    end do
    c%sign=1; call trim(c)
  end subroutine subabs

  subroutine badd(a,b,c)
    type(big), intent(in) :: a,b
    type(big), intent(out) :: c
    integer :: order
    nullify(c%d); c%sign=0
    if(r_status/=0) return
    if(a%sign==0) then
      call bc(b,c); return
    else if(b%sign==0) then
      call bc(a,c); return
    end if
    if(a%sign==b%sign) then
      call addabs(a,b,c); c%sign=a%sign
    else
      order=cmpabs(a,b)
      if(order>=0) then
        call subabs(a,b,c)
        if(c%sign/=0) c%sign=a%sign
      else
        call subabs(b,a,c)
        if(c%sign/=0) c%sign=b%sign
      end if
    end if
  end subroutine badd

  subroutine bmul(a,b,c)
    type(big), intent(in) :: a,b
    type(big), intent(out) :: c
    integer :: i,j,k
    integer(ik) :: v,carry
    nullify(c%d); c%sign=0
    if(r_status/=0) return
    call bn(c,size(a%d)+size(b%d)+1)
    if(r_status/=0) return
    do i=1,size(a%d)
      carry=0_ik
      do j=1,size(b%d)
        k=i+j-1; v=c%d(k)+a%d(i)*b%d(j)+carry
        c%d(k)=mod(v,base); carry=v/base
      end do
      k=i+size(b%d)
      do while(carry>0_ik)
        v=c%d(k)+carry; c%d(k)=mod(v,base); carry=v/base; k=k+1
      end do
    end do
    c%sign=a%sign*b%sign; call trim(c)
  end subroutine bmul

  subroutine bsmall(a,k,c)
    type(big), intent(in) :: a
    integer(ik), intent(in) :: k
    type(big), intent(out) :: c
    integer(ik) :: carry,v
    integer :: i
    nullify(c%d); c%sign=0
    if(r_status/=0) return
    call bn(c,size(a%d)+1); carry=0_ik
    if(r_status/=0) return
    do i=1,size(a%d)
      v=a%d(i)*k+carry; c%d(i)=mod(v,base); carry=v/base
    end do
    c%d(size(a%d)+1)=carry; c%sign=1; call trim(c)
  end subroutine bsmall

  subroutine bdiv(a,b,q,r)
    type(big), intent(in) :: a,b
    type(big), intent(out) :: q,r
    type(big) :: v,tmp,next
    integer :: i
    integer(ik) :: lo,hi,mid
    nullify(q%d,r%d); q%sign=0; r%sign=0
    if(r_status/=0) return
    call bn(q,size(a%d)); call bi(0_ik,r)
    if(r_status/=0) return
    if(b%sign==0) then
      r_status=4; return
    end if
    do i=size(a%d),1,-1
      call bn(next,size(r%d)+1)
      if(r_status/=0) return
      next%d(2:)=r%d; next%d(1)=a%d(i); next%sign=1; call trim(next)
      if(r_status/=0) then
        call bz(next); return
      end if
      call bz(r); r=next; nullify(next%d)
      lo=0_ik; hi=base-1_ik
      do while(lo<hi)
        mid=(lo+hi+1_ik)/2_ik
        call bsmall(b,mid,v)
        if(r_status/=0) then
          call bz(v); return
        end if
        if(cmpabs(v,r)<=0) then
          lo=mid
        else
          hi=mid-1_ik
        end if
        call bz(v)
      end do
      q%d(i)=lo
      if(lo>0_ik) then
        call bsmall(b,lo,v)
        if(r_status/=0) then
          call bz(v); return
        end if
        call subabs(r,v,tmp)
        if(r_status/=0) then
          call bz(v); call bz(tmp); return
        end if
        call bz(r); call bz(v); r=tmp; nullify(tmp%d)
      end if
    end do
    q%sign=a%sign*b%sign; call trim(q)
    if(r%sign/=0) r%sign=a%sign
  end subroutine bdiv

  subroutine bgcd(a,b,g)
    type(big), intent(in) :: a,b
    type(big), intent(out) :: g
    type(big) :: x,y,q,r
    nullify(g%d); g%sign=0
    if(r_status/=0) return
    call bc(a,x); call bc(b,y)
    if(r_status/=0) then
      call bz(x); call bz(y); return
    end if
    if(x%sign/=0) x%sign=1
    if(y%sign/=0) y%sign=1
    do while(y%sign/=0.and.r_status==0)
      call bdiv(x,y,q,r); call bz(q); call bz(x)
      x=y; nullify(y%d); y=r; nullify(r%d)
    end do
    call bz(y); g=x; nullify(x%d)
  end subroutine bgcd

  function keep(n,q) result(id)
    type(big), intent(inout) :: n,q
    integer :: id,newcap,st,i
    type(big) :: g,nn,qq,rem
    type(rational), pointer :: tmp(:)
    id=r0
    if(r_status/=0) then
      call bz(n); call bz(q); return
    end if
    if(q%sign==0) then
      r_status=4; call bz(n); call bz(q); return
    end if
    if(n%sign==0.and.used>=1) then
      call bz(n); call bz(q); return
    end if
    if(q%sign<0) then
      q%sign=1; n%sign=-n%sign
    end if
    call bgcd(n,q,g)
    if(r_status/=0) then
      call bz(g); call bz(n); call bz(q); return
    end if
    call bdiv(n,g,nn,rem); call bz(rem)
    if(r_status/=0) then
      call bz(nn); call bz(g); call bz(n); call bz(q); return
    end if
    call bdiv(q,g,qq,rem); call bz(rem); call bz(g); call bz(n); call bz(q)
    if(r_status/=0) then
      call bz(nn); call bz(qq); return
    end if
    if(used==capacity) then
      if(capacity>huge(0)/2) then
        r_status=3; call bz(nn); call bz(qq); return
      end if
      newcap=max(256,2*capacity)
      if(.not.may_allocate()) then
        call bz(nn); call bz(qq); return
      end if
      allocate(tmp(newcap),stat=st)
      if(st/=0) then
        r_status=3; call bz(nn); call bz(qq); return
      end if
      do i=1,newcap
        nullify(tmp(i)%n%d,tmp(i)%q%d)
        tmp(i)%n%sign=0; tmp(i)%q%sign=0
      end do
      do i=1,used
        tmp(i)=arena(i)
      end do
      if(arena_live) deallocate(arena)
      arena=>tmp; arena_live=.true.; capacity=newcap
    end if
    used=used+1; arena(used)%n=nn; arena(used)%q=qq
    nullify(nn%d); nullify(qq%d); id=used
  end function keep

  subroutine r_start()
    type(big) :: n,q
    call r_finish(); r_status=0; allocation_count=0
    call bi(0_ik,n); call bi(1_ik,q); r0=keep(n,q)
    call bi(1_ik,n); call bi(1_ik,q); r1=keep(n,q)
  end subroutine r_start

  subroutine r_finish()
    integer :: i
    if(arena_live) then
      do i=1,used
        call bz(arena(i)%n); call bz(arena(i)%q)
      end do
      deallocate(arena); nullify(arena)
    end if
    used=0; capacity=0; arena_live=.false.
  end subroutine r_finish

  function ri(v) result(id)
    integer(ik), intent(in) :: v
    integer :: id
    type(big) :: n,q
    id=r0
    if(r_status/=0) return
    if(v==0_ik) return
    if(v==1_ik) then
      id=r1; return
    end if
    call bi(v,n); call bi(1_ik,q); id=keep(n,q)
  end function ri

  function rnum(a) result(id)
    integer, intent(in) :: a
    integer :: id
    type(big) :: n,q
    id=r0
    if(r_status/=0) return
    call bc(arena(a)%n,n); call bi(1_ik,q); id=keep(n,q)
  end function rnum

  function rden(a) result(id)
    integer, intent(in) :: a
    integer :: id
    type(big) :: n,q
    id=r0
    if(r_status/=0) return
    call bc(arena(a)%q,n); call bi(1_ik,q); id=keep(n,q)
  end function rden

  function ra(a,b) result(id)
    integer, intent(in) :: a,b
    integer :: id
    type(big) :: l,r,n,q
    id=r0
    if(r_status/=0) return
    if(rz(a)) then
      id=b; return
    else if(rz(b)) then
      id=a; return
    end if
    call bmul(arena(a)%n,arena(b)%q,l); call bmul(arena(b)%n,arena(a)%q,r)
    call badd(l,r,n); call bmul(arena(a)%q,arena(b)%q,q)
    call bz(l); call bz(r); id=keep(n,q)
  end function ra

  function rn(a) result(id)
    integer, intent(in) :: a
    integer :: id
    type(big) :: n,q
    id=r0
    if(r_status/=0.or.rz(a)) return
    call bc(arena(a)%n,n); call bc(arena(a)%q,q); n%sign=-n%sign; id=keep(n,q)
  end function rn

  function rs(a,b) result(id)
    integer, intent(in) :: a,b
    integer :: id,neg
    neg=rn(b); id=ra(a,neg)
  end function rs

  function rm(a,b) result(id)
    integer, intent(in) :: a,b
    integer :: id
    type(big) :: n,q
    id=r0
    if(r_status/=0.or.rz(a).or.rz(b)) return
    call bmul(arena(a)%n,arena(b)%n,n); call bmul(arena(a)%q,arena(b)%q,q)
    id=keep(n,q)
  end function rm

  function rd(a,b) result(id)
    integer, intent(in) :: a,b
    integer :: id
    type(big) :: n,q
    id=r0
    if(r_status/=0) return
    if(rz(b)) then
      r_status=4; return
    end if
    if(rz(a)) return
    call bmul(arena(a)%n,arena(b)%q,n); call bmul(arena(a)%q,arena(b)%n,q)
    id=keep(n,q)
  end function rd

  function rc(a,b) result(c)
    integer, intent(in) :: a,b
    integer :: c
    type(big) :: l,r
    c=0
    if(r_status/=0) return
    if(arena(a)%n%sign/=arena(b)%n%sign) then
      c=1
      if(arena(a)%n%sign<arena(b)%n%sign) c=-1
      return
    end if
    if(rz(a)) return
    call bmul(arena(a)%n,arena(b)%q,l); call bmul(arena(b)%n,arena(a)%q,r)
    if(r_status/=0) then
      call bz(l); call bz(r); return
    end if
    c=cmpabs(l,r)*arena(a)%n%sign; call bz(l); call bz(r)
  end function rc

  function rz(a) result(z)
    integer, intent(in) :: a
    logical :: z
    z=.true.
    if(r_status/=0) return
    z=(arena(a)%n%sign==0)
  end function rz

  function rzint(a) result(z)
    integer, intent(in) :: a
    logical :: z
    z=.false.
    if(r_status/=0) return
    if(size(arena(a)%q%d)/=1) return
    z=(arena(a)%q%d(1)==1_ik)
  end function rzint

  function rf(a) result(id)
    integer, intent(in) :: a
    integer :: id
    type(big) :: n,q,rem,one,next
    id=r0
    if(r_status/=0) return
    call bdiv(arena(a)%n,arena(a)%q,n,rem)
    if(arena(a)%n%sign<0.and.rem%sign/=0) then
      call bi(-1_ik,one); call badd(n,one,next); call bz(one); call bz(n)
      n=next; nullify(next%d)
    end if
    call bz(rem); call bi(1_ik,q); id=keep(n,q)
  end function rf

  function rroot(a) result(id)
    integer, intent(in) :: a
    integer :: id,lo,hi,mid,two
    id=r0
    if(r_status/=0) return
    if(rc(a,r0)<0) then
      r_status=4; return
    end if
    if(rz(a)) return
    lo=r0; hi=r1; two=ri(2_ik)
    do while(rc(rm(hi,hi),a)<0.and.r_status==0)
      hi=rm(hi,two)
    end do
    do while(rc(rs(hi,lo),r1)>0.and.r_status==0)
      mid=rf(rd(ra(lo,hi),two))
      if(rc(rm(mid,mid),a)>=0) then
        hi=mid
      else
        lo=mid
      end if
    end do
    id=hi
  end function rroot

  function rtoi(a,status) result(v)
    integer, intent(in) :: a
    integer, intent(out) :: status
    integer(ik) :: v,lim,digit
    integer :: j
    status=0; v=0_ik
    if(.not.rzint(a)) then
      status=4; return
    end if
    lim=-huge(v)
    if(arena(a)%n%sign<0) lim=lim-1_ik
    do j=size(arena(a)%n%d),1,-1
      digit=arena(a)%n%d(j)
      if(v<(lim+digit)/base) then
        status=2; v=0_ik; return
      end if
      v=v*base-digit
    end do
    if(arena(a)%n%sign>0) v=-v
  end function rtoi
end module sp_rational
