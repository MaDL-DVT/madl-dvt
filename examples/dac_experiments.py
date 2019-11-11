import os
import subprocess
import time

dir = os.getcwd()
gng_dir = os.path.join(dir,'go_no_go')
pc_dir = os.path.join(dir,'power_clock')

gng_name = 'go_no_go_top'
gng_suffixes = ['1','1_dl','3','3_dl','7','7_dl','11','11_dl','15','15_dl','23','23_dl']

pc_name = 'pc_top'
pc_suffixes = ['1_2','1_2_dl','1_3','1_3_dl','2_2','2_2_dl','3_2','3_2_dl']

results_name = "results.txt"

def run_test(tname,suffixes,res_file):
    for i in suffixes:
        f = tname + '_' + i + '.madl'
        name = os.path.join(dir,'go_no_go',f)
        start_time = time.time()
        gng_res = subprocess.run(['time','dlockdetect','-f',name,'--no-cyclecheck','--simultaneous-smt','--smt-only'], stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        res_file.write(f + '\t\t\t' + 'smt' + '\t' + str(time.time()-start_time) + '\n')
        start_time = time.time()
        gng_res = subprocess.run(['time','dlockdetect','-f',name,'--no-cyclecheck','--simultaneous-smt','--reachability-only'], stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        res_file.write(f + '\t\t\t' + 'smv' + '\t' + str(time.time()-start_time) + '\n')

file = open(results_name,'w+')

run_test(gng_name,gng_suffixes,file)
run_test(pc_name,pc_suffixes,file)

file.close()
