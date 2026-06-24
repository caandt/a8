#include <LIEF/LIEF.hpp>
#include <vector>
#include <cstdint>

extern "C" {

typedef void ELFHandle;

ELFHandle* lief_parse(const char* filepath) {
    return LIEF::ELF::Parser::parse(filepath).release();
}

const uint32_t* lief_get_text(ELFHandle* handle, size_t* out_elements, uint64_t* va) {
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);
    for (LIEF::ELF::Segment& seg : bin->segments()) {
        if (seg.has(LIEF::ELF::Segment::FLAGS::X)) {
            auto content = seg.content();
            *out_elements = content.size() / 4;
            *va = seg.virtual_address();
            return reinterpret_cast<const uint32_t*>(content.data());
        }
    }
    *out_elements = 0;
    return nullptr;
}

uint64_t lief_get_after(ELFHandle* handle) {
    auto elf = static_cast<LIEF::ELF::Binary*>(handle);
    uint64_t max = 0;
    for (LIEF::ELF::Segment& seg : elf->segments()) {
        max = std::max(max, seg.virtual_address() + seg.virtual_size());
    }
    return ((max >> 12) + 1) << 12;
}

uint64_t lief_get_entrypoint(ELFHandle* handle) {
    return static_cast<LIEF::ELF::Binary*>(handle)->header().entrypoint();
}

void lief_set_nx(ELFHandle* handle) {
    auto elf = static_cast<LIEF::ELF::Binary*>(handle);
    for (LIEF::ELF::Segment& seg : elf->segments()) {
        if (seg.has(LIEF::ELF::Segment::FLAGS::X)) {
            uint32_t flags = static_cast<uint32_t>(seg.flags());
            flags &= ~static_cast<uint32_t>(LIEF::ELF::Segment::FLAGS::X);
            seg.flags(flags);
        }
    }
}

void lief_set_entrypoint(ELFHandle* handle, uint64_t entrypoint) {
    static_cast<LIEF::ELF::Binary*>(handle)->header().entrypoint(entrypoint);
}

void lief_add_segment(ELFHandle* handle, const uint32_t* data, size_t elements, uint64_t va) {
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
}

void lief_write_and_free(ELFHandle* handle, const char* out_path) {
    auto bin = static_cast<LIEF::ELF::Binary*>(handle);
    bin->write(out_path);
    delete bin;
}

// force the linker to keep this file in the archive
void _force_link() {}

}
