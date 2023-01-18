#!/usr/bin/ruby
# coding: utf-8

require 'open3'
require 'timeout'
require 'csv'
require 'optparse'

def execution(params, cmd, benchname)
  system(cmd)
end

params = ARGV.getopts('', 'bin:./_build/default/bin/main.exe',
                      'args: --problem psat --format smt-lib2 -mbi bench_info.csv',
                      'bench:./benchmarks/chc-comp18/lia',
                      'recursive',
                      'ext:.smt2')

binname = ' ' + params['bin']
bin = binname
# output = params['output']
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

bench_files.each_key { |bench|
  STDOUT.print '|'
  STDOUT.flush
  begin
    execution(params, cmd + bench, bench)
  rescue Interrupt
    puts "Abort bench.rs"
    exit
  end
}
