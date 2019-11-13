import os
import subprocess
import time
import errno

curdir = os.getcwd()
gng_dir = os.path.join(curdir,'go_no_go')
pc_dir = os.path.join(curdir,'power_clock')

gng_name = 'go_no_go_top'
gng_suffixes = ['1','1_dl','3','3_dl','7','7_dl','11','11_dl','15','15_dl','23','23_dl']

pc_name = 'pc_top'
pc_suffixes = ['1_2','1_2_dl','1_3','1_3_dl','2_2','2_2_dl','3_2','3_2_dl']

results_name = "results.txt"

def check_dlockdetect_exists():
    # Call raises an exception if command falls
    subprocess.check_call(['dlockdetect', '--help'],
                          stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)

def run_test(tdir,tname,suffixes,res_file):
    for i in suffixes:
        f = tname + '_' + i + '.madl'
        name = os.path.join(curdir,tdir,f)
        print("Testing {0} using SMT solver".format(name))
        start_time = time.time()
        gng_res = subprocess.run(['time','dlockdetect','-f',name,'--no-cyclecheck','--simultaneous-smt','--smt-only'], stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        if gng_res.returncode < 0:
            print("Case {0}, SMT failed with exit code {1}".format(name, gng_res.returncode))
        res_file.write(f + '\t\t\t' + 'smt' + '\t' + str(time.time()-start_time) + '\n')
        start_time = time.time()
        print("Testing {0} using nuXMV (reachability)".format(name))
        gng_res = subprocess.run(['time','dlockdetect','-f',name,'--no-cyclecheck','--simultaneous-smt','--reachability-only'], stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        if gng_res.returncode < 0:
            print("Case {0}, reachability failed with exit code {1}".format(
                name, gng_res.returncode))
        res_file.write(f + '\t\t\t' + 'smv' + '\t' + str(time.time()-start_time) + '\n')

check_dlockdetect_exists()

resfile = open(results_name,'w+')

run_test('go_no_go',gng_name,gng_suffixes,resfile)
run_test('power_clock',pc_name,pc_suffixes,resfile)

resfile.close()
