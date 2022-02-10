// TODO: This is a tweaked version of qoiconv.c
//  Figure out if we can "distribute it", along with stb_image

/*

Command line tool to convert between png <> qoi format

Requires "stb_image.h" and "stb_image_write.h"
Compile with:
	gcc qoiconv.c -std=c99 -O3 -o qoiconv

Dominic Szablewski - https://phoboslab.org


-- LICENSE: The MIT License(MIT)

Copyright(c) 2021 Dominic Szablewski

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files(the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and / or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions :
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

*/


#define STB_IMAGE_IMPLEMENTATION
#define STBI_ONLY_PNG
#define STBI_NO_LINEAR
#include "stb_image.h"

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

#include "stainless.h"


#define STR_ENDS_WITH(S, E) (strcmp(S + strlen(S) - (sizeof(E)-1), E) == 0)

int qoi_read_helper(const char *filename, void **pixels, int *w, int *h, int *channels) {
    FILE *f = fopen(filename, "rb");

    if (!f) {
        return 0;
    }

    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    if (size <= 0) {
        fclose(f);
        return 0;
    }
    fseek(f, 0, SEEK_SET);

    int8_t *data = malloc(size);
    if (!data) {
        fclose(f);
        return 0;
    }

    size_t bytes_read = fread(data, 1, size, f);
    fclose(f);
    if (bytes_read != size) {
        return 0;
    }

    OptionMut_0_DecodedResult_0 decoded_res = decode((array_int8) { .data = data, .length = size }, size);
    free(data);
    if (decoded_res.tag == tag_SomeMut_0_DecodedResult_0) {
        *pixels = decoded_res.value.SomeMut_0_DecodedResult_0_v.v_21.pixels_5.data;
        *w = decoded_res.value.SomeMut_0_DecodedResult_0_v.v_21.w_3;
        *h = decoded_res.value.SomeMut_0_DecodedResult_0_v.v_21.h_56;
        *channels = decoded_res.value.SomeMut_0_DecodedResult_0_v.v_21.chan_14;
        return 1;
    } else {
        return 0;
    }
}

int qoi_write_helper(const char *filename, void *pixels, int w, int h, int channels) {
    FILE *f = fopen(filename, "wb");

    if (!f) {
        return 0;
    }

    OptionMut_0_EncodedResult_0 encoded_res = encode((array_int8) { .data = pixels, .length = w * h * channels }, w, h, channels);
    if (encoded_res.tag == tag_SomeMut_0_EncodedResult_0) {
        int8_t *data = encoded_res.value.SomeMut_0_EncodedResult_0_v.v_21.encoded_0.data;
        int64_t len = encoded_res.value.SomeMut_0_EncodedResult_0_v.v_21.length_1;
        size_t written = fwrite(data, 1, len, f);
        fclose(f);
        free(data);
        return written == len;
    } else {
        return 0;
    }
}

int main(int argc, char **argv) {
	if (argc < 3) {
		puts("Usage: verified-qoiconv <infile> <outfile>");
		puts("Examples:");
		puts("  verified-qoiconv input.png output.qoi");
		puts("  verified-qoiconv input.qoi output.png");
		exit(1);
	}

	void *pixels = NULL;
	int w, h, channels;
	if (STR_ENDS_WITH(argv[1], ".png")) {
		if(!stbi_info(argv[1], &w, &h, &channels)) {
			printf("Couldn't read header %s\n", argv[1]);
			exit(1);
		}

		// Force all odd encodings to be RGBA
		if(channels != 3) {
			channels = 4;
		}

		pixels = (void *)stbi_load(argv[1], &w, &h, NULL, channels);
	}
	else if (STR_ENDS_WITH(argv[1], ".qoi")) {
	    qoi_read_helper(argv[1], &pixels, &w, &h, &channels);
	}

	if (pixels == NULL) {
		printf("Couldn't load/decode %s\n", argv[1]);
		exit(1);
	}

	int encoded = 0;
	if (STR_ENDS_WITH(argv[2], ".png")) {
		encoded = stbi_write_png(argv[2], w, h, channels, pixels, 0);
	}
	else if (STR_ENDS_WITH(argv[2], ".qoi")) {
		encoded = qoi_write_helper(argv[2], pixels, w, h, channels);
	}

	if (!encoded) {
		printf("Couldn't write/encode %s\n", argv[2]);
		exit(1);
	}

	free(pixels);
	return 0;
}
