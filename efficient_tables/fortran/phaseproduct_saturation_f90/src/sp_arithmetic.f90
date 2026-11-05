! Cost arithmetic copied from the separately preserved phaseproduct_f90 implementation.
module sp_arithmetic
  implicit none
  private
  integer, parameter :: ik = selected_int_kind(18)
  integer(ik), parameter :: INF = huge(0_ik)
  integer, parameter :: mantissa_bits = 28
  integer, parameter :: limb_bits = 26, limb_count = 1700
  integer(ik), parameter :: limb_base = 67108864_ik
  public :: ik, INF, sat_add, sat_mul, tau_exact, leaf_cost, child_width

contains

  function sat_add(x, y) result(value)
    integer(ik), intent(in) :: x, y
    integer(ik) :: value
    value = INF
    if (x < 0_ik .or. y < 0_ik) return
    if (x > INF - y) return
    value = x + y
  end function sat_add

  function sat_mul(x, y) result(value)
    integer(ik), intent(in) :: x, y
    integer(ik) :: value
    value = INF
    if (x < 0_ik .or. y < 0_ik) return
    if (x == 0_ik .or. y == 0_ik) then
      value = 0_ik
      return
    end if
    if (x > INF / y) return
    value = x * y
  end function sat_mul

  function bit_length(value) result(bits)
    integer(ik), intent(in) :: value
    integer :: bits
    integer(ik) :: remaining
    remaining = value
    bits = 0
    do while (remaining > 0_ik)
      remaining = remaining / 2_ik
      bits = bits + 1
    end do
  end function bit_length

  subroutine normalize_interval(lower, upper, exponent)
    integer(ik), intent(inout) :: lower, upper
    integer, intent(inout) :: exponent
    integer :: shift
    integer(ik) :: divisor, remainder
    ! Preserve lower*2**exponent <= exact <= upper*2**exponent.
    ! Rounded upper has at most 29 bits; multiplying two such bounds
    ! never exceeds 2**56. No real arithmetic or logarithm is used.
    shift = max(0, bit_length(upper) - mantissa_bits)
    if (shift == 0) return
    divisor = 2_ik ** shift
    remainder = mod(upper, divisor)
    lower = lower / divisor
    upper = upper / divisor
    if (remainder /= 0_ik) upper = upper + 1_ik
    exponent = exponent + shift
  end subroutine normalize_interval

  subroutine interval_multiply(xlo, xhi, xe, ylo, yhi, ye, zlo, zhi, ze)
    integer(ik), intent(in) :: xlo, xhi, ylo, yhi
    integer, intent(in) :: xe, ye
    integer(ik), intent(out) :: zlo, zhi
    integer, intent(out) :: ze
    zlo = xlo * ylo
    zhi = xhi * yhi
    ze = xe + ye
    call normalize_interval(zlo, zhi, ze)
  end subroutine interval_multiply

  function tau_full(rotations) result(value)
    integer(ik), intent(in) :: rotations
    integer :: value
    integer(ik) :: digits(limb_count), work(limb_count), factor(3)
    integer(ik) :: remaining, carry
    integer :: used, factor_used, next_used, i, j, iteration, bits
    ! R <= 2**63-1, hence 100*R < 2**70 and (100*R)**615 < 2**43050.
    ! 1700 base-2**26 limbs hold 44200 bits. Factor has at most three
    ! limbs. Each uncarried product sum is below 3*2**52 + 2**28,
    ! so every intermediate fits a signed selected_int_kind(18).
    factor = 0_ik
    remaining = rotations
    factor_used = 0
    do while (remaining > 0_ik)
      factor_used = factor_used + 1
      factor(factor_used) = mod(remaining, limb_base)
      remaining = remaining / limb_base
    end do
    carry = 0_ik
    do i = 1, factor_used
      remaining = factor(i) * 100_ik + carry
      factor(i) = mod(remaining, limb_base)
      carry = remaining / limb_base
    end do
    if (carry > 0_ik) then
      factor_used = factor_used + 1
      factor(factor_used) = carry
    end if
    digits = 0_ik
    digits(1) = 1_ik
    used = 1
    do iteration = 1, 615
      next_used = used + factor_used
      work(1:next_used) = 0_ik
      do j = 1, factor_used
        do i = 1, used
          work(i + j - 1) = work(i + j - 1) + digits(i) * factor(j)
        end do
      end do
      carry = 0_ik
      do i = 1, next_used
        remaining = work(i) + carry
        digits(i) = mod(remaining, limb_base)
        carry = remaining / limb_base
      end do
      used = next_used
      do while (digits(used) == 0_ik .and. used > 1)
        used = used - 1
      end do
    end do
    bits = (used - 1) * limb_bits + bit_length(digits(used))
    value = (bits - 1 + 272) / 200
  end function tau_full

  function tau_exact(rotations) result(value)
    integer(ik), intent(in) :: rotations
    integer :: value
    integer(ik) :: flo, fhi, rlo, rhi, tlo, thi
    integer :: fe, re, te, power, lower_tau, upper_tau
    ! The public domain is R>=0. tau(0)=1 follows the specified convention.
    if (rotations <= 0_ik) then
      value = 1
      return
    end if
    flo = rotations
    fhi = rotations
    fe = 0
    call normalize_interval(flo, fhi, fe)
    flo = flo * 100_ik
    fhi = fhi * 100_ik
    call normalize_interval(flo, fhi, fe)
    rlo = 1_ik
    rhi = 1_ik
    re = 0
    power = 615
    do while (power > 0)
      if (mod(power, 2) == 1) then
        call interval_multiply(rlo, rhi, re, flo, fhi, fe, tlo, thi, te)
        rlo = tlo
        rhi = thi
        re = te
      end if
      power = power / 2
      if (power > 0) then
        call interval_multiply(flo, fhi, fe, flo, fhi, fe, tlo, thi, te)
        flo = tlo
        fhi = thi
        fe = te
      end if
    end do
    ! Monotonicity of floor(log2(x)) gives certified integer endpoints.
    ! Equal rounded endpoints certify tau; ambiguity uses the full power.
    lower_tau = (bit_length(rlo) - 1 + re + 272) / 200
    upper_tau = (bit_length(rhi) - 1 + re + 272) / 200
    if (lower_tau == upper_tau) then
      value = lower_tau
    else
      value = tau_full(rotations)
    end if
  end function tau_exact

  function leaf_cost(multiplicity, width) result(value)
    integer(ik), intent(in) :: multiplicity
    integer, intent(in) :: width
    integer(ik) :: value, rotations
    value = INF
    if (multiplicity < 0_ik .or. width < 0) return
    rotations = sat_mul(multiplicity, int(width, ik))
    rotations = sat_mul(rotations, int(width, ik))
    if (rotations == INF) return
    value = sat_mul(rotations, int(4 + tau_exact(rotations), ik))
  end function leaf_cost

  function child_width(width, arity, a, b) result(value)
    integer, intent(in) :: width, arity, a, b
    integer :: value
    integer(ik) :: extra, total
    value = huge(0)
    if (width < 0 .or. arity < 2 .or. a < 0 .or. b < 0) return
    extra = sat_add(int(mod(width, arity), ik), int(b, ik))
    extra = max(int(a, ik), extra)
    total = sat_add(int(width / arity, ik), 1_ik)
    total = sat_add(total, extra)
    if (total > int(huge(0), ik)) return
    value = int(total)
  end function child_width

end module sp_arithmetic
