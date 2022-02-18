# Benchmark results
Below are the results of running `genc-qoibench` with 3 runs on the `images` folder.

The tests were executed on an Ubuntu 20.04.3 LTS with an Intel Core i7-7700HQ CPU @ 2.80GHz processor. GCC 9.3.0 was used for compilation.

## Average over all images

|             |decode ms| encode ms| decode mpps| encode mpps|  size kb|  rate|
|-------------|--------:|---------:|-----------:|-----------:|--------:|-----:|
|**stbi**     |    191.0|    1429.8|       40.35|        5.39|    15744| 69.7%|
|**qoi**      |     53.9|      72.1|      143.08|      106.85|    12576| 55.7%|
|**genc_qoi** |     63.2|     101.3|      121.85|       76.07|    12576| 55.7%|


## By image
### Bridalveil_Fall_and_valley.png (of size 4288x3216)

|             |decode ms| encode ms| decode mpps| encode mpps|  size kb|  rate|
|-------------|--------:|---------:|-----------:|-----------:|--------:|-----:|
|**stbi**     |    349.0|    2570.6|       39.51|        5.36|    30542| 75.6%|
|**qoi**      |    108.8|     131.4|      126.75|      104.97|    24889| 61.6%|
|**genc_qoi** |    122.4|     183.0|      112.66|       75.37|    24889| 61.6%|

### Central_Bern_from_north.png (of size 2913x2204)

|             |decode ms| encode ms| decode mpps| encode mpps|  size kb|  rate|
|-------------|--------:|---------:|-----------:|-----------:|--------:|-----:|
|**stbi**     |    190.8|    1235.4|       33.64|        5.20|    14883| 79.1%|
|**qoi**      |     38.0|      60.2|      168.97|      106.58|    11511| 61.2%|
|**genc_qoi** |     47.5|      86.7|      135.02|       74.08|    11511| 61.2%|

### Chocolate_Hills_overview.png (of size 2592x1944)

|             |decode ms| encode ms| decode mpps| encode mpps|  size kb|  rate|
|-------------|--------:|---------:|-----------:|-----------:|--------:|-----:|
|**stbi**     |    120.0|     966.2|       41.99|        5.21|    11024| 74.7%|
|**qoi**      |     31.4|      47.1|      160.23|      107.08|     8452| 57.3%|
|**genc_qoi** |     38.9|      67.6|      129.58|       74.57|     8452| 57.3%|

### Eyjafjallajokull_sous_les_aurores_boreales.png (of size 3000x1638)

|             |decode ms| encode ms| decode mpps| encode mpps|  size kb|  rate|
|-------------|--------:|---------:|-----------:|-----------:|--------:|-----:|
|**stbi**     |     80.0|     809.6|       61.40|        6.07|     5968| 41.5%|
|**qoi**      |     38.5|      43.1|      127.52|      113.95|     5226| 36.3%|
|**genc_qoi** |     43.4|      57.7|      113.33|       85.23|     5226| 36.3%|

### Linze_Zhangye_Gansu_China_panoramio_4.png (of size 3597x2163)

|             |decode ms| encode ms| decode mpps| encode mpps|  size kb|  rate|
|-------------|--------:|---------:|-----------:|-----------:|--------:|-----:|
|**stbi**     |    164.6|    1511.9|       47.27|        5.15|    17749| 77.9%|
|**qoi**      |     48.0|      73.7|      162.16|      105.51|    13206| 57.9%|
|**genc_qoi** |     59.0|     106.1|      131.93|       73.32|    13206| 57.9%|

### Plaigne_2.png (of size 3840x2160)

|             |decode ms| encode ms| decode mpps| encode mpps|  size kb|  rate|
|-------------|--------:|---------:|-----------:|-----------:|--------:|-----:|
|**stbi**     |    241.4|    1485.2|       34.36|        5.58|    14298| 58.8%|
|**qoi**      |     58.4|      77.2|      142.02|      107.45|    12170| 50.1%|
|**genc_qoi** |     68.3|     106.9|      121.44|       77.63|    12170| 50.1%|
