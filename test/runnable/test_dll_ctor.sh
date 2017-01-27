#!/usr/bin/env bash

dir=${RESULTS_DIR}/runnable
dmddir=${RESULTS_DIR}${SEP}runnable
output_file=${dir}/test_dll_ctor.sh.out

rm -f ${output_file}

if [ "${OS}" == "win64" ]; then
    winmodel=64
elif [ "${OS}" == "win32" ]; then
    winmodel=32mscoff
else
    echo "Skipping shared library test on ${OS}."
    touch ${output_file}
    exit 0
fi

die()
{
    cat ${output_file}
    rm -f ${output_file}
    exit 1
}


$DMD -m${winmodel} -of${dmddir}/test_dll_ctor_b.dll runnable/imports/test_dll_ctor_b.d -shared -defaultlib=phobos${winmodel}s.lib \
    -L/IMPLIB:${dmddir}/test_dll_ctor_b.lib >> ${output_file}
if [ $? -ne 0 ]; then die; fi

$DMD -m${winmodel} -of${dmddir}/test_dll_ctor_a.dll runnable/imports/test_dll_ctor_a.d -shared -defaultlib=phobos${winmodel}s.lib \
    -Irunnable/imports ${dmddir}/test_dll_ctor_b.lib -L/IMPLIB:${dmddir}/test_dll_ctor_a.lib  >> ${output_file}
if [ $? -ne 0 ]; then die; fi

$DMD -m${winmodel} -of${dmddir}/test_dll_ctor${EXE} runnable/extra-files/test_dll_ctor.d -useShared -defaultlib=phobos${winmodel}s.lib \
    -Irunnable/imports ${dmddir}/test_dll_ctor_b.lib ${dmddir}/test_dll_ctor_a.lib >> ${output_file}
if [ $? -ne 0 ]; then die; fi

desired="shared module ctor of b
shared module ctor of a
module ctor of a
shared module ctor of exe
main
shared module dtor of exe
module dtor of a
shared module dtor of a
shared module dtor of b"

result=`${dmddir}/test_dll_ctor${EXE} | tr -d '\r'` # need to remove \r from '\r\n' in output to match
echo "$result" >> ${output_file}

if [ "$desired" = "$result" ]; then
    exit 0
else
    echo "*** Error: got above but was expecting:" >> ${output_file}
    echo "$desired" >> ${output_file}
    die
fi
