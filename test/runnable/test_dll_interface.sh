#!/usr/bin/env bash

dir=${RESULTS_DIR}/runnable
dmddir=${RESULTS_DIR}${SEP}runnable
output_file=${dir}/test_dll_interface.sh.out

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

$DMD -m${winmodel} -of${dmddir}/test_dll_interface_c.dll runnable/imports/test_dll_interface_c.d -shared -defaultlib=phobos${winmodel}s.lib >> ${output_file}
if [ $? -ne 0 ]; then die; fi

$DMD -m${winmodel} -of${dmddir}/test_dll_interface_a.dll runnable/imports/test_dll_interface_a.d -shared -defaultlib=phobos${winmodel}s.lib \
    -Irunnable/imports -L/IMPLIB:${dmddir}/test_dll_interface_a.lib  >> ${output_file}
if [ $? -ne 0 ]; then die; fi

$DMD -m${winmodel} -of${dmddir}/test_dll_interface_b.dll runnable/imports/test_dll_interface_b.d -shared -defaultlib=phobos${winmodel}s.lib \
    -Irunnable/imports ${dmddir}/test_dll_interface_a.lib >> ${output_file}
if [ $? -ne 0 ]; then die; fi

$DMD -m${winmodel} -of${dmddir}/test_dll_interface${EXE} runnable/extra-files/test_dll_interface.d -useShared -defaultlib=phobos${winmodel}s.lib \
    -Irunnable/imports ${dmddir}/test_dll_interface_b.lib ${dmddir}/test_dll_interface_a.lib >> ${output_file}
if [ $? -ne 0 ]; then die; fi

${dmddir}/test_dll_interface${EXE} >> ${output_file}
if [ $? -ne 0 ]; then die; fi
