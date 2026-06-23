#include <LIEF/LIEF.hpp>
#include <vector>
#include <cstdint>

extern "C" {

typedef void ELFHandle;

ELFHandle* lief_parse(const char* filepath) {
    try {
        auto elf = LIEF::ELF::Parser::parse(filepath);
        if (!elf) return nullptr;
        return elf.release();
    } catch (...) {
        return nullptr;
    }
}

const uint32_t* lief_get_text(ELFHandle* handle, size_t* out_elements) {
    if (!handle) return nullptr;
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);
    for (LIEF::ELF::Segment& seg : bin->segments()) {
        if (seg.has(LIEF::ELF::Segment::FLAGS::X)) {
            auto content = seg.content();
            *out_elements = content.size() / 4;
            return reinterpret_cast<const uint32_t*>(content.data());
        }
    }
    *out_elements = 0;
    return nullptr;
}

int lief_set_entrypoint(ELFHandle* handle, uint64_t entrypoint) {
    if (!handle) return -1;
    try {
        auto bin = static_cast<LIEF::ELF::Binary*>(handle);
        for (LIEF::ELF::Segment& seg : bin->segments()) {
            if (seg.has(LIEF::ELF::Segment::FLAGS::X)) {
                uint32_t flags = static_cast<uint32_t>(seg.flags());
                flags &= ~static_cast<uint32_t>(LIEF::ELF::Segment::FLAGS::X);
                seg.flags(flags);
            }
        }
        bin->header().entrypoint(entrypoint);
        return 0;
    } catch (...) {
        return -2;
    }
}
int lief_add_segment(ELFHandle* handle, const uint32_t* data, size_t elements, uint64_t va) {
    if (!handle) return -1;
    try {
        auto bin = static_cast<LIEF::ELF::Binary*>(handle);

        LIEF::ELF::Segment new_seg;
        new_seg.type(LIEF::ELF::Segment::TYPE::LOAD);
        uint32_t rx_flags = static_cast<uint32_t>(LIEF::ELF::Segment::FLAGS::R) |
                            static_cast<uint32_t>(LIEF::ELF::Segment::FLAGS::X);
        new_seg.flags(rx_flags);

        auto byte_ptr = reinterpret_cast<const uint8_t*>(data);
        size_t byte_size = elements * 4;
        new_seg.content(std::vector<uint8_t>(byte_ptr, byte_ptr + byte_size));
        new_seg.virtual_address(va);
        bin->add(new_seg);

        return 0;
    } catch (...) {
        return -2;
    }
}

void lief_write_and_free(ELFHandle* handle, const char* out_path) {
    if (!handle) return;
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);
    bin->write(out_path);
    delete bin;
}

}
