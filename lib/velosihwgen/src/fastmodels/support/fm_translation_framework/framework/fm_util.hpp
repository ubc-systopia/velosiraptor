#ifndef _FM_UTIL_H_
#define _FM_UTIL_H_ 1

#include <map>
#include <vector>
#include <string>
#include "types.hpp"
#include "logging.hpp"

#ifndef TEST_MOCK_FAST_MODELS

#include "pv/DVM.h"
#include "pv/PVBusAddr.h"
#include "pv/PVTransaction.h"  // for pv::Tx_Result
#include "pv/PVBusMaster.h"
#include "pv/PVAccessWidth.h"
#else

namespace pv {
    struct Tx_Result;
    struct ReadTransaction;
    struct WriteTransaction;
}
namespace DVM {
    typedef uint32_t error_response_t;
    struct Message;
}
#endif

bool read_paddr(pv::RandomContextTransactionGenerator *ptw_pvbus, lpaddr_t paddr, uint8_t width, uint64_t *data);

#endif
