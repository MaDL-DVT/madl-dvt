import os
import subprocess
import time
import errno
from sys import argv

curdir = os.getcwd()
gng_dir = os.path.join(curdir,'go_no_go')
pc_dir = os.path.join(curdir,'power_clock')

gng_name = 'go_no_go_top'
gng_suffixes = ['1','1_dl','2','2_dl','3','3_dl','4','4_dl','5','5_dl','6','6_dl','7','7_dl']

pc_name = 'pc_top'
pc_suffixes = ['1_5','1_5_dl','10_5','10_5_dl','20_5','20_5_dl','30_5','30_5_dl','40_5','40_5_dl','50_5','50_5_dl']


if (len(argv) > 1):
    results_name = argv[1]
else:
    results_name = 'results.txt'

def check_dlockdetect_exists():
    # Call raises an exception if command falls
    subprocess.check_call(['dlockdetect', '--help'],
                          stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)

def run_test_smt(tdir,tname,suffixes,res_file):
    for i in suffixes:
        f = tname + '_' + i + '.madl'
        name = os.path.join(curdir,tdir,f)
        print("Testing {0} using SMT solver".format(name))
        start_time = time.time()
        gng_res = subprocess.run(['time','dlockdetect','-f',name,'--no-cyclecheck','--simultaneous-smt','--smt-only'], stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        if gng_res.returncode < 0:
            print("Case {0}, SMT failed with exit code {1}".format(name, gng_res.returncode))
        print(str(time.time()-start_time))
        res_file.write(f + '\t\t\t' + 'smt' + '\t' + str(time.time()-start_time) + '\n')

def run_test_smv(tdir,tname,suffixes,res_file):
    for i in suffixes:
        f = tname + '_' + i + '.madl'
        name = os.path.join(curdir,tdir,f)
        start_time = time.time()
        print("Testing {0} using nuXMV (reachability)".format(name))
        gng_res = subprocess.run(['time','dlockdetect','-f',name,'--no-cyclecheck','--simultaneous-smt','--reachability-only'], stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        if gng_res.returncode < 0:
            print("Case {0}, reachability failed with exit code {1}".format(
                name, gng_res.returncode))
        res_file.write(f + '\t\t\t' + 'smv' + '\t' + str(time.time()-start_time) + '\n')
        print(str(time.time()-start_time))

check_dlockdetect_exists()

resfile = open(results_name,'w+')

run_test_smt('go_no_go',gng_name,gng_suffixes,resfile)
run_test_smt('power_clock',pc_name,pc_suffixes,resfile)
run_test_smv('go_no_go',gng_name,gng_suffixes,resfile)
run_test_smv('power_clock',pc_name,pc_suffixes,resfile)

resfile.close()
