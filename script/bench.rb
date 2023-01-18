#!/usr/bin/ruby
# coding: utf-8

# usage:
# e.g.) ./bench.rb --bin './build/default/bin/main.exe' --args '--algorithm rec-limit --format smt-lib2 --valid' --bench './benchmarks/chc-comp18'

require 'open3'
require 'timeout'
require 'csv'
require 'optparse'

def result_of(output)
  case output
  when "valid", "invalid", "unknown", "sat", "unsat"
    output
  else
    "abort"
  end
end

def exe_timeout(params, cmd, benchname, output)
  ## timeout for the process that does not work OCaml's timeout.
  params['timeout'] ||= "100"
  result = [benchname]
  Open3.popen2e(cmd) { |_, stdout_err, wait_thr|
    begin
      pid = wait_thr.pid
      tmp = ''
      start = Time.now
      Timeout.timeout(params['timeout'].to_i) { # set timeout
        while line = stdout_err.gets
          tmp += line
        end
      }
      finish = Time.now
      result.push (result_of tmp.chomp)
      result.push (finish - start)
    rescue Timeout::Error
      result.push "#{params['timeout'].to_i} Time Out"
      Process.kill('KILL', pid)
    rescue Interrupt
      result.push 'Interrupted (Killed by Ctrl-C)'
      Process.Kill('KILL', pid)
      sleep(1)
    end
  }
  output << result
end

def exe_without_timeout(param, cmd, benchname, output)
  result = [benchname]
  Open3.popen2e(cmd) { |_, stdout_err, wait_thr|
    begin
      pid = wait_thr.pid
      tmp = ''
      start = Time.now
      while line = stdout_err.gets
        tmp += line
      end
      finish = Time.now
      result.push (result_of tmp.chomp)
      result.push (finish - start)
    rescue Interrupt
      result.push 'Interrupted (Killed by Ctrl-C)'
      Process.Kill('KILL', pid)
      sleep(1)
    end
  }
  output << result
end

def execution(params, cmd, benchname, output)
  if benchname.include?("-invalid") or benchname.include? "-fail" then
    cmd += " --mode disprove"
  end
  if params['timeout']
    exe_timeout(params, cmd, benchname, output)
  else
    exe_without_timeout(params, cmd, benchname, output)
  end
end

`dune build`

params = ARGV.getopts('', 'bin:./_build/default/bin/main.exe',
                      'args: --format smt-lib2',
                      'bench:./benchmarks/chc-comp18/lia',
                      'recursive',
                      'timeout:',
                      'ext:.smt2',
                      'output:./output.csv')

binname = ' ' + params['bin']
bin = binname
# bin = binname + '.bench '
# system('cp ' + binname + bin)
output = params['output']
arg = ' ' + params['args'] + ' '
cmd = bin + arg

if File.directory?(params['bench'])
  bench_dir = params['bench']
  search_query = if params['recursive']
                   '/**/*' + params['ext']
                 else
                   '/*' + params['ext']
                 end
  bench_files = {}
  Dir.glob(bench_dir + search_query).sort.each { |f|
    bench_files[f] = File.stat(f).size
  }
else
  bench_files = { params['bench'] => 0 }
end

# bench_files = Hash[bench_files.sort_by { |_, v| v }] # sort benchmarks by size
CSV.open(output, 'w') { |output_f|
  date = Time.now.strftime('%Y-%m-%d:%H:%M%S')
  output_f << [date, cmd]

  bench_files.each_key { |bench|
    STDOUT.print '|'
    STDOUT.flush
    begin
      execution(params, cmd + bench, bench, output_f)
    rescue Interrupt
      puts "Abort bench.rs"
      exit
    end
  }
}
