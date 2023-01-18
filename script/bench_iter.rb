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
      result.push (result_of tmp.chomp.split(",")[0])
      result.push (finish - start)
      result.push (tmp.chomp.split(",")[1].chomp)
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
      result.push (result_of tmp.chomp.split(",")[0])
      result.push (finish - start)
      result.push (tmp.chomp.split(",")[1].chomp)
    rescue Interrupt
      result.push 'Interrupted (Killed by Ctrl-C)'
      Process.Kill('KILL', pid)
      sleep(1)
    end
  }
  output << result
end

def exe_timeout_2(params, cmd, benchname, output)
  ## timeout for the process that does not work OCaml's timeout.
  params['timeout'] ||= "100"
  result = [benchname]
  Open3.popen3(cmd) { |_, stdout, _, wait_thr|
    begin
      pid = wait_thr.pid
      tmp = ''
      start = Time.now
      Timeout.timeout(params['timeout'].to_i) { # set timeout
        while line = stdout.gets
          tmp += line
        end
      }
      finish = Time.now
      result.push (result_of tmp.chomp.split(",")[0])
      result.push (finish - start)
      result.push (tmp.chomp.split(",")[1].chomp)
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

def exe_without_timeout_2(param, cmd, benchname, output)
  result = [benchname]
  Open3.popen2e(cmd) { |_, stdout, _, wait_thr|
    begin
      pid = wait_thr.pid
      tmp = ''
      start = Time.now
      while line = stdout.gets
        tmp += line
      end
      finish = Time.now
      result.push (result_of tmp.chomp.split(",")[0])
      result.push (finish - start)
      result.push (tmp.chomp.split(",")[1].chomp)
    rescue Interrupt
      result.push 'Interrupted (Killed by Ctrl-C)'
      Process.Kill('KILL', pid)
      sleep(1)
    end
  }
  output << result
end

def execution(params, cmd, benchname, output, synthesizer)
  if benchname.include?("-invalid") or benchname.include? "-fail" then
    cmd += " --mode disprove"
  end
  if params['timeout']
    if synthesizer == "bp" || synthesizer == "pasid"
      exe_timeout_2(params, cmd, benchname, output)
    else
      exe_timeout(params, cmd, benchname, output)
    end
  else
    if synthesizer == "bp" || synthesizer == "pasid"
      exe_without_timeout_2(params, cmd, benchname, output)
    else
      exe_without_timeout(params, cmd, benchname, output)
    end
  end
end

`dune build`

params = ARGV.getopts('', 'bin:./_build/default/bin/main.exe',
                      'args: --synthesizer tb',
                      'bench:./benchmarks/sygus-comp/comp/2017/Inv_Track',
                      'recursive',
                      'timeout:',
                      'ext:.sl',
                      'output:./output.csv')

binname = ' ' + params['bin']
bin = binname
# bin = binname + '.bench '
# system('cp ' + binname + bin)
output = params['output']
arg = ' ' + params['args'] + ' --problem psat --output-iteration ' + ' '
cmd = bin + arg

idx = 0
synthesizer = "tb"
params['args'].split(" ").each_with_index { |w, i|
  if (w == "--synthesizer" || w ==  "-synth")
    idx = i+1
  end
}
if idx > 0
  synthesizer = params['args'].split(" ")[idx]
end

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
      execution(params, cmd + bench, bench, output_f, synthesizer)
    rescue Interrupt
      puts "Abort bench.rs"
      exit
    end
  }
}

