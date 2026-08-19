csv = "benchmark.csv"
png = "benchmark.png"

if (!exists("max_value")) max_value = 1000000
set encoding utf8

last_n(col) = real(system(sprintf("awk -F, 'NR > 1 && $%d != \"\" { n = $1 } END { print n }' %s", col, csv)))
last_ms(col) = real(system(sprintf("awk -F, 'NR > 1 && $%d != \"\" { ms = $%d } END { print ms }' %s", col, col, csv)))
avg_ms_at_sizes(col, sizes) = real(system(sprintf("awk -F, 'BEGIN { split(\"%s\", sizes, \" \"); for (i in sizes) want[sizes[i]] = 1 } NR > 1 && want[$1] && $%d != \"\" { total += $%d; count += 1 } END { print total / count }' %s", sizes, col, col, csv)))

insertion_n = last_n(2)
insertion_ms = last_ms(2)
merge_n = last_n(3)
merge_ms = last_ms(3)
counting_n = last_n(4)
counting_ms = last_ms(4)
counting_overhead_ms = avg_ms_at_sizes(4, "4 8 16")

n2(x) = insertion_ms * (x**2) / (insertion_n**2)
nlogn(x) = x <= 1 ? 1/0 : merge_ms * (x * log(x) / log(2)) / (merge_n * log(merge_n) / log(2))
nk(x) = counting_overhead_ms + (counting_ms - counting_overhead_ms) * x / counting_n

set terminal pngcairo size 1652,790 enhanced font "Helvetica,24"
set output png

set datafile separator comma
set title "Sorting Benchmark"
set xlabel "Size of List"
set ylabel "Time"

set logscale x 2
set logscale y 10
set xrange [1:*]
set yrange [0.000001:10000]

set grid ytics
set key box right bottom

set xtics ("2^{0}" 1, "2^{1}" 2, "2^{2}" 4, "2^{4}" 16, "2^{6}" 64, \
  "2^{8}" 256, "2^{10}" 1024, "2^{12}" 4096, "2^{14}" 16384, \
  "2^{16}" 65536, "2^{18}" 262144, "2^{20}" 1048576, \
  "2^{22}" 4194304, "2^{24}" 16777216, "2^{26}" 67108864)
set ytics ("1 ns" 0.000001, "10 ns" 0.00001, "100 ns" 0.0001, \
  "1 μs" 0.001, "10 μs" 0.01, "100 μs" 0.1, \
  "1 ms" 1, "10 ms" 10, "100 ms" 100, \
  "1 s" 1000, "10 s" 10000)

plot \
  csv using 1:2 title "Insertion Sort" with points pointtype 7 pointsize 1.8 linecolor rgb "#159bed", \
  csv using 1:3 title "Merge Sort" with points pointtype 5 pointsize 1.8 linecolor rgb "#55d63a", \
  csv using 1:4 title "Counting Sort" with points pointtype 9 pointsize 1.8 linecolor rgb "#f02114", \
  n2(x) title "N^2" with lines linewidth 2 linecolor rgb "#159bed", \
  nlogn(x) title "N log n" with lines linewidth 2 linecolor rgb "#55d63a", \
  nk(x) title "N + k" with lines linewidth 2 linecolor rgb "#f02114"
