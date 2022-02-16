#!/bin/bash

make genc-qoiconv
mkdir -p ../results

# Encoding
./genc-qoiconv ../images/Bridalveil_Fall_and_valley.png ../results/Bridalveil_Fall_and_valley.qoi
cmp -l ../images/Bridalveil_Fall_and_valley.qoi ../results/Bridalveil_Fall_and_valley.qoi

./genc-qoiconv ../images/Central_Bern_from_north.png ../results/Central_Bern_from_north.qoi
cmp -l ../images/Central_Bern_from_north.qoi ../results/Central_Bern_from_north.qoi

./genc-qoiconv ../images/Chocolate_Hills_overview.png ../results/Chocolate_Hills_overview.qoi
cmp -l ../images/Chocolate_Hills_overview.qoi ../results/Chocolate_Hills_overview.qoi

./genc-qoiconv ../images/Eyjafjallajokull_sous_les_aurores_boreales.png ../results/Eyjafjallajokull_sous_les_aurores_boreales.qoi
cmp -l ../images/Eyjafjallajokull_sous_les_aurores_boreales.qoi ../results/Eyjafjallajokull_sous_les_aurores_boreales.qoi

./genc-qoiconv ../images/Linze_Zhangye_Gansu_China_panoramio_4.png ../results/Linze_Zhangye_Gansu_China_panoramio_4.qoi
cmp -l ../images/Linze_Zhangye_Gansu_China_panoramio_4.qoi ../results/Linze_Zhangye_Gansu_China_panoramio_4.qoi

./genc-qoiconv ../images/Plaigne_2.png ../results/Plaigne_2.qoi
cmp -l ../images/Plaigne_2.qoi ../results/Plaigne_2.qoi


# Decoding
./genc-qoiconv ../images/Bridalveil_Fall_and_valley.qoi ../results/Bridalveil_Fall_and_valley.png
./genc-qoiconv ../images/Central_Bern_from_north.qoi ../results/Central_Bern_from_north.png
./genc-qoiconv ../images/Chocolate_Hills_overview.qoi ../results/Chocolate_Hills_overview.png
./genc-qoiconv ../images/Eyjafjallajokull_sous_les_aurores_boreales.qoi ../results/Eyjafjallajokull_sous_les_aurores_boreales.png
./genc-qoiconv ../images/Linze_Zhangye_Gansu_China_panoramio_4.qoi ../results/Linze_Zhangye_Gansu_China_panoramio_4.png
./genc-qoiconv ../images/Plaigne_2.qoi ../results/Plaigne_2.png