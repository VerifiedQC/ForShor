program phaseproduct_saturation
  use sp_outer, only: solve_pp
  implicit none
  integer :: n,kmax,ios
  logical :: use_bounds
  namelist /run/ n,kmax,use_bounds
  n=40
  kmax=3
  use_bounds=.true.
  read(*,nml=run,iostat=ios)
  if (ios/=0) then
    write(*,*) 'ERROR expected &run n=40, kmax=3, use_bounds=.true. / on standard input'
    stop 1
  end if
  call solve_pp(n,kmax,use_bounds)
end program phaseproduct_saturation
