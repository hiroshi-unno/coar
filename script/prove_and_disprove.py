#-*- code:utf-8 -*-

from multiprocessing import Pool
from multiprocessing import Manager
import time
import sys
import subprocess
from subprocess import TimeoutExpired
from subprocess import Popen
from subprocess import PIPE
import traceback

ground_children = Manager().list()

def run_coar(args, timeout):
    cmd = "dune exec main -- " + args
    start = time.time()
    with Popen([cmd], stdout=PIPE, shell=True) as p:
#        print("opend")
        ground_children.append(p.pid)
#        print("append")
        try:
            p.wait(timeout=timeout)
            elapsed = time.time() - start
            res = p.stdout.read().decode("utf-8").rstrip('\n')
            res_ = list(map(lambda s: s.lstrip(' '), res.split(",")))
            if len(res_) == 2:
                res, ite = list(map(lambda s: s.lstrip(' '), res.split(",")))
                if res in ["sat", "unsat"]:
                    return (res, elapsed, ite)
            elif len(res_) == 1:
                if res in ["valid", "invalid"]:
                    return (res, elapsed, None)
            else:
                return ("abort", elapsed, None)
        except TimeoutExpired:
            p.kill()
            return ("timeout", timeout, None)

def prove(args, timeout):
#    print("prove")
    return run_coar("-m prove -oi " + args, timeout)

def disprove(args, timeout):
#    print("disprove")
    return run_coar("-m disprove -oi " + args, timeout)

def run_my_process(opts, target, timeout):
    pool = Pool(processes=2)
    def call_back_f(result):
        res, time, ite = result
        print("{}, {}, {}, {}".format(target, res, time, ite))
#        print("delete_gcs")
        for gc in ground_children:
#            print("gc:{}".format(gc))
            subprocess.run(["kill {}".format(gc)], shell=True)
            #gc.kill()
        pool.terminate()

    cmd_args = opts + " " + target

    res1 = pool.apply_async(prove, args=(cmd_args, timeout), callback=call_back_f)
    res2 = pool.apply_async(disprove, args=(cmd_args, timeout), callback=call_back_f)

    pool.close()
    pool.join()

if __name__ == "__main__":
    args = sys.argv
    timeout = float(args[1])
    opts = args[2]
    target = args[3]
#    print("********* opts: {}".format(opts))
#    print("********* target: {}".format(target))
    run_my_process(opts, target, timeout)
