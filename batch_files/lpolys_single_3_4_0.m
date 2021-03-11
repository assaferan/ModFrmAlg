AttachSpec("spec");
import "tests/tests.m" : get_lpolys;
time0 := Cputime();
get_lpolys(3, [4, 0]);
printf "elapsed: %o\n", Cputime()-time0;
exit;
