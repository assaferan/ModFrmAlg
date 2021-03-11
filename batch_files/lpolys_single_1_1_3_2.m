AttachSpec("spec");
import "tests/tests.m" : get_lpolys;
time0 := Cputime();
get_lpolys(1, 1, [3, 2]);
printf "elapsed: %o\n", Cputime()-time0;
exit;
