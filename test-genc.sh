#!/bin/bash

# https://superuser.com/a/125408
function bindiff {
    cmp -l "$1" "$2" | gawk '{printf "%08X %02X %02X\n", $1, strtonum(0$2), strtonum(0$3)}'
}

mkdir -p results

# Encoding
./genc/verified-qoiconv images/Bridalveil_Fall_and_valley.png results/Bridalveil_Fall_and_valley.qoi
bindiff images/Bridalveil_Fall_and_valley.qoi results/Bridalveil_Fall_and_valley.qoi

./genc/verified-qoiconv images/Central_Bern_from_north.png results/Central_Bern_from_north.qoi
bindiff images/Central_Bern_from_north.qoi results/Central_Bern_from_north.qoi

./genc/verified-qoiconv images/Chocolate_Hills_overview.png results/Chocolate_Hills_overview.qoi
bindiff images/Chocolate_Hills_overview.qoi results/Chocolate_Hills_overview.qoi

./genc/verified-qoiconv images/Eyjafjallajokull_sous_les_aurores_boreales.png results/Eyjafjallajokull_sous_les_aurores_boreales.qoi
bindiff images/Eyjafjallajokull_sous_les_aurores_boreales.qoi results/Eyjafjallajokull_sous_les_aurores_boreales.qoi

./genc/verified-qoiconv images/Linze_Zhangye_Gansu_China_panoramio_4.png results/Linze_Zhangye_Gansu_China_panoramio_4.qoi
bindiff images/Linze_Zhangye_Gansu_China_panoramio_4.qoi results/Linze_Zhangye_Gansu_China_panoramio_4.qoi

./genc/verified-qoiconv images/Plaigne_2.png results/Plaigne_2.qoi
bindiff images/Plaigne_2.qoi results/Plaigne_2.qoi


# Decoding
./genc/verified-qoiconv images/Bridalveil_Fall_and_valley.qoi results/Bridalveil_Fall_and_valley.png
./genc/verified-qoiconv images/Central_Bern_from_north.qoi results/Central_Bern_from_north.png
./genc/verified-qoiconv images/Chocolate_Hills_overview.qoi results/Chocolate_Hills_overview.png
./genc/verified-qoiconv images/Eyjafjallajokull_sous_les_aurores_boreales.qoi results/Eyjafjallajokull_sous_les_aurores_boreales.png
./genc/verified-qoiconv images/Linze_Zhangye_Gansu_China_panoramio_4.qoi results/Linze_Zhangye_Gansu_China_panoramio_4.png
./genc/verified-qoiconv images/Plaigne_2.qoi results/Plaigne_2.png