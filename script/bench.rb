#!/usr/bin/ruby
# coding: utf-8

# usage:
# e.g.) ./bench.rb --bin './_build/default/main.exe' --args '--algorithm rec-limit --format smt-lib2 --valid' --bench './benchmarks/chc-comp18'

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

# The reason of a refusal -- exit status 1 with a last stderr line `error: <reason>`, the
# shape in which the tool declines an input -- or nil for any other run (a crash exits 2
# or by a signal, and a line on stdout is never read as one).
def refusal_of(status, err)
  return nil unless status && status.exitstatus == 1
  line = err.scrub('?').lines.map(&:chomp).select { |l| l.start_with?('error: ') }.last
  line && line.delete_prefix('error: ')
end

# The verdict of a finished run.  As before stdout and stderr were told apart, the run is
# an answer only when it printed nothing but a verdict (stderr included); otherwise it is
# `refused` (with its reason) or `abort`.
def verdict_of(out, err, status)
  return [result_of(out.chomp)] if err.empty?
  reason = refusal_of(status, err)
  reason ? ['refused', reason] : ['abort']
end

# run_command: runs CMD with stdout and stderr read apart (stderr in a thread, so that
# neither pipe can fill and stall the solver), within LIMIT seconds when LIMIT is given.
def run_command(cmd, benchname, output, limit)
  result = [benchname]
  Open3.popen3(cmd) { |_, stdout, stderr, wait_thr|
    pid = wait_thr.pid
    # popen3 closes the pipes when its block ends, which a reader still waiting after a
    # timeout meets as IOError: that run's stderr is not needed.
    err_reader = Thread.new { begin stderr.read rescue IOError '' end }
    err_reader.report_on_exception = false
    begin
      tmp = ''
      start = Time.now
      read = proc {
        while line = stdout.gets
          tmp += line
        end
      }
      limit ? Timeout.timeout(limit, &read) : read.call
      status = wait_thr.value
      finish = Time.now
      err = err_reader.value
      STDERR.print err
      verdict, reason = verdict_of(tmp, err, status)
      result.push verdict
      result.push (finish - start)
      result.push reason if reason
    rescue Timeout::Error
      result.push "#{limit} Time Out"
      Process.kill('KILL', pid)
    rescue Interrupt
      result.push 'Interrupted (Killed by Ctrl-C)'
      Process.kill('KILL', pid)
      sleep(1)
    end
  }
  output << result
end

def exe_timeout(params, cmd, benchname, output)
  ## timeout for the process that does not work OCaml's timeout.
  params['timeout'] ||= "100"
  run_command(cmd, benchname, output, params['timeout'].to_i)
end

def exe_without_timeout(param, cmd, benchname, output)
  run_command(cmd, benchname, output, nil)
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

params = ARGV.getopts('', 'bin:./_build/default/main.exe',
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
