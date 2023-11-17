#include <vrs_test.h>

int vrs_test() {
    MSG("VRS: Velosiraptor tests starting.\n");

    void *translation_unit_data = (void*)0xC0000000UL;
    void *translation_unit_control = (void *)0x1C0000000UL;

    uint32_t *data32 = (uint32_t *)translation_unit_data;

    MSG("VRS: reading %p (32)\n", data32);
    MSG("VRS: reading %p (32) = %u\n", data32, *data32);

    MSG("VRS: writing %p (32)\n", data32);
    *data32 = 0x12345678;

    MSG("VRS: reading %p (32)\n", data32);
    MSG("VRS: reading %p (32) = %u\n", data32, *data32);


    uint64_t *data64 = (uint64_t *)translation_unit_data;

    MSG("VRS: reading %p (64)\n", data64);
    MSG("VRS: reading %p (64) = %u\n", data64, *data64);

    MSG("VRS: writing %p (64)\n", data64);
    *data32 = 0x12345678;

    MSG("VRS: reading %p (64)\n", data64);
    MSG("VRS: reading %p (64) = %u\n", data64, *data64);


    MSG("Velosiraptor tests completed.\n");

    return 0;
}
