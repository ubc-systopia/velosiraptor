#include "fm_util.hpp"

bool read_paddr(pv::RandomContextTransactionGenerator *ptw_pvbus, lpaddr_t paddr, uint8_t width, uint64_t *data) {
    pv::AccessWidth access_width;

    Logging::debug("TranslationUnitBase::read_paddr(0x%lx, width %u)", paddr, width);

    if (ptw_pvbus == nullptr) {
        Logging::error("TranslationUnitBase::read_paddr - no page walker set!");
        return false;
    }

    if (width == 64) {
        access_width = pv::ACCESS_64_BITS;
    } else if (width == 32) {
        access_width = pv::ACCESS_32_BITS;
    } else {
        return false;
    }

    // buffer descriptor
    pv::RandomContextTransactionGenerator::buffer_t bt
        = pv::RandomContextTransactionGenerator::buffer_t(access_width, data, 1);

    // transaction attributes
    pv::TransactionAttributes ta = pv::TransactionAttributes();
    ta.setPTW(true);

    pv::ACERequest req = pv::ACERequest();
    pv::Tx_Result res = ptw_pvbus->read(&ta, &req, (pv::bus_addr_t)paddr, &bt);
    return res.isOK();
}
