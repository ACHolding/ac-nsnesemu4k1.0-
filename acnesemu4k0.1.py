# acnesemu4k.py
# MewNES — single-file NES emulator with FCEUX-style chrome
# Pure-Python core: 6502 CPU + PPU (bg + sprites) + mappers 0/1/2/3
# 60 FPS target (best-effort in CPython). No audio yet.

import os
import sys
import time
import json
import tkinter as tk
from tkinter import filedialog, messagebox

try:
    from PIL import Image, ImageTk
    HAS_PIL = True
except ImportError:
    HAS_PIL = False

FILES_OFF = False

WINDOW_TITLE = "FCEUX 2.6.6 — AC's NES Emulator 0.2 (MewNES)"
ROM_FILTER = [
    ("NES ROM", "*.nes"),
    ("FDS disk", "*.fds"),
    ("All supported", "*.nes *.fds"),
    ("All files", "*.*"),
]
STATE_EXT = ".acs0"

NES_WIDTH = 256
NES_HEIGHT = 240
SCALE = 3
FPS_TARGET = 60.0988
FRAME_TIME = 1.0 / FPS_TARGET

BG = "#d4d0c8"
BG_DARK = "#808080"
FG = "#000000"
STATUS_BG = "#ffffff"
CANVAS_BORDER = 2

INES_MAGIC = b"NES\x1a"
FDS_MAGIC = b"FDS\x1a"

# NES master palette (RGB triplets, 64 entries)
NES_PALETTE = [
    (0x54,0x54,0x54),(0x00,0x1E,0x74),(0x08,0x10,0x90),(0x30,0x00,0x88),
    (0x44,0x00,0x64),(0x5C,0x00,0x30),(0x54,0x04,0x00),(0x3C,0x18,0x00),
    (0x20,0x2A,0x00),(0x08,0x3A,0x00),(0x00,0x40,0x00),(0x00,0x3C,0x00),
    (0x00,0x32,0x3C),(0x00,0x00,0x00),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0x98,0x96,0x98),(0x08,0x4C,0xC4),(0x30,0x32,0xEC),(0x5C,0x1E,0xE4),
    (0x88,0x14,0xB0),(0xA0,0x14,0x64),(0x98,0x22,0x20),(0x78,0x3C,0x00),
    (0x54,0x5A,0x00),(0x28,0x72,0x00),(0x08,0x7C,0x00),(0x00,0x76,0x28),
    (0x00,0x66,0x78),(0x00,0x00,0x00),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0xEC,0xEE,0xEC),(0x4C,0x9A,0xEC),(0x78,0x7C,0xEC),(0xB0,0x62,0xEC),
    (0xE4,0x54,0xEC),(0xEC,0x58,0xB4),(0xEC,0x6A,0x64),(0xD4,0x88,0x20),
    (0xA0,0xAA,0x00),(0x74,0xC4,0x00),(0x4C,0xD0,0x20),(0x38,0xCC,0x6C),
    (0x38,0xB4,0xCC),(0x3C,0x3C,0x3C),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0xEC,0xEE,0xEC),(0xA8,0xCC,0xEC),(0xBC,0xBC,0xEC),(0xD4,0xB2,0xEC),
    (0xEC,0xAE,0xEC),(0xEC,0xAE,0xD4),(0xEC,0xB4,0xB0),(0xE4,0xC4,0x90),
    (0xCC,0xD2,0x78),(0xB4,0xDE,0x78),(0xA8,0xE2,0x90),(0x98,0xE2,0xB4),
    (0xA0,0xD6,0xE4),(0xA0,0xA2,0xA0),(0x00,0x00,0x00),(0x00,0x00,0x00),
]
PAL_R = bytes(c[0] for c in NES_PALETTE)
PAL_G = bytes(c[1] for c in NES_PALETTE)
PAL_B = bytes(c[2] for c in NES_PALETTE)

# Mirroring modes
MIRROR_H = 0
MIRROR_V = 1
MIRROR_4 = 2
MIRROR_SL = 3  # single screen lower
MIRROR_SU = 4  # single screen upper

# CPU flag bits
F_C = 0x01
F_Z = 0x02
F_I = 0x04
F_D = 0x08
F_B = 0x10
F_U = 0x20
F_V = 0x40
F_N = 0x80


# ============================================================
# ROM loader
# ============================================================

class NESROM:
    def __init__(self):
        self.path = None
        self.data = None
        self.name = None
        self.format = None
        self.mapper = 0
        self.submapper = 0
        self.prg_banks = 0
        self.chr_banks = 0
        self.prg_size = 0
        self.chr_size = 0
        self.prg = b""
        self.chr = bytearray()
        self.chr_is_ram = False
        self.mirroring = MIRROR_H
        self.battery = False
        self.trainer = b""
        self.prg_ram_size = 8 * 1024
        self.ines2 = False

    @property
    def loaded(self):
        return self.data is not None

    def load(self, path):
        path = os.path.abspath(path)
        with open(path, "rb") as f:
            raw = f.read()
        if len(raw) < 16:
            return False, "File is too small to be a valid ROM."
        if raw[:4] == INES_MAGIC:
            return self._load_ines(path, raw)
        if raw[:4] == FDS_MAGIC or path.lower().endswith(".fds"):
            return self._load_fds(path, raw)
        if path.lower().endswith(".nes"):
            return False, "Missing iNES header (expected NES\\x1A)."
        return False, "Unrecognized ROM format."

    def _load_ines(self, path, raw):
        flags6 = raw[6]
        flags7 = raw[7]
        ines2 = (flags7 & 0x0C) == 0x08
        self.ines2 = ines2

        prg_banks_low = raw[4]
        chr_banks_low = raw[5]
        if ines2:
            prg_banks_high = raw[9] & 0x0F
            chr_banks_high = (raw[9] >> 4) & 0x0F
            self.prg_banks = prg_banks_low | (prg_banks_high << 8)
            self.chr_banks = chr_banks_low | (chr_banks_high << 8)
            self.mapper = (flags7 & 0xF0) | (flags6 >> 4) | ((raw[8] & 0x0F) << 8)
            self.submapper = (raw[8] >> 4) & 0x0F
        else:
            self.prg_banks = prg_banks_low
            self.chr_banks = chr_banks_low
            self.mapper = (flags7 & 0xF0) | (flags6 >> 4)
            self.submapper = 0

        self.prg_size = self.prg_banks * 16 * 1024
        self.chr_size = self.chr_banks * 8 * 1024

        if flags6 & 0x08:
            self.mirroring = MIRROR_4
        elif flags6 & 0x01:
            self.mirroring = MIRROR_V
        else:
            self.mirroring = MIRROR_H

        self.battery = bool(flags6 & 0x02)
        has_trainer = bool(flags6 & 0x04)

        header_len = 16
        offset = header_len
        if has_trainer:
            self.trainer = bytes(raw[offset:offset + 512])
            offset += 512
        else:
            self.trainer = b""

        end_prg = offset + self.prg_size
        if len(raw) < end_prg:
            return False, f"ROM truncated (expected at least {end_prg} bytes)."
        self.prg = bytes(raw[offset:end_prg])
        offset = end_prg

        end_chr = offset + self.chr_size
        if self.chr_size > 0:
            if len(raw) < end_chr:
                return False, "CHR section truncated."
            self.chr = bytearray(raw[offset:end_chr])
            self.chr_is_ram = False
        else:
            self.chr = bytearray(8 * 1024)
            self.chr_is_ram = True
            self.chr_size = 8 * 1024

        self.path = path
        self.data = raw
        self.name = os.path.basename(path)
        self.format = "NES 2.0" if ines2 else "iNES"
        return True, None

    def _load_fds(self, path, raw):
        self.path = path
        self.data = raw
        self.name = os.path.basename(path)
        self.format = "FDS"
        self.mapper = 0
        self.prg_size = len(raw)
        return False, "FDS playback not implemented yet."

    def close(self):
        self.__init__()

    def info_line(self):
        if not self.loaded:
            return ""
        m = ["Horizontal","Vertical","Four-screen","SingleL","SingleU"][self.mirroring]
        return (f"{self.name} | {self.format} | Mapper {self.mapper} | "
                f"PRG {self.prg_size//1024}K CHR {self.chr_size//1024}K | {m}")


# ============================================================
# Mappers
# ============================================================

class Mapper:
    def __init__(self, rom):
        self.rom = rom
        self.prg = rom.prg
        self.chr = rom.chr
        self.chr_is_ram = rom.chr_is_ram
        self.prg_ram = bytearray(rom.prg_ram_size)
        self.mirroring = rom.mirroring
        self.irq_pending = False

    def cpu_read(self, addr):
        return 0
    def cpu_write(self, addr, value):
        pass
    def ppu_read(self, addr):
        return self.chr[addr & 0x1FFF]
    def ppu_write(self, addr, value):
        if self.chr_is_ram:
            self.chr[addr & 0x1FFF] = value & 0xFF
    def on_scanline(self):
        pass
    def reset(self):
        pass


class Mapper0(Mapper):
    # NROM: 16K or 32K PRG, fixed bank(s), no banking
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if addr >= 0x8000:
            off = (addr - 0x8000) % len(self.prg)
            return self.prg[off]
        return 0
    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF


class Mapper2(Mapper):
    # UxROM: 16KB switchable at $8000, fixed last bank at $C000, CHR-RAM
    def __init__(self, rom):
        super().__init__(rom)
        self.bank = 0
        self.num_banks = len(self.prg) // 0x4000
        self.last_bank = self.num_banks - 1
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if 0x8000 <= addr < 0xC000:
            return self.prg[self.bank * 0x4000 + (addr - 0x8000)]
        if addr >= 0xC000:
            return self.prg[self.last_bank * 0x4000 + (addr - 0xC000)]
        return 0
    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF
        elif addr >= 0x8000:
            self.bank = value & 0x0F
            if self.bank >= self.num_banks:
                self.bank %= self.num_banks


class Mapper3(Mapper):
    # CNROM: fixed PRG, switchable 8KB CHR
    def __init__(self, rom):
        super().__init__(rom)
        self.chr_bank = 0
        self.num_chr_banks = max(1, len(self.chr) // 0x2000)
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if addr >= 0x8000:
            return self.prg[(addr - 0x8000) % len(self.prg)]
        return 0
    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF
        elif addr >= 0x8000:
            self.chr_bank = (value & 0x03) % self.num_chr_banks
    def ppu_read(self, addr):
        return self.chr[self.chr_bank * 0x2000 + (addr & 0x1FFF)]
    def ppu_write(self, addr, value):
        if self.chr_is_ram:
            self.chr[self.chr_bank * 0x2000 + (addr & 0x1FFF)] = value & 0xFF


class Mapper1(Mapper):
    # MMC1
    def __init__(self, rom):
        super().__init__(rom)
        self.shift = 0x10
        self.control = 0x0C  # 16K mode, fixed last bank
        self.chr_bank0 = 0
        self.chr_bank1 = 0
        self.prg_bank = 0
        self.num_prg_banks = len(self.prg) // 0x4000
        self.num_chr_banks = max(1, len(self.chr) // 0x1000)
        self._apply_mirroring()
    def _apply_mirroring(self):
        m = self.control & 0x03
        if m == 0: self.mirroring = MIRROR_SL
        elif m == 1: self.mirroring = MIRROR_SU
        elif m == 2: self.mirroring = MIRROR_V
        else: self.mirroring = MIRROR_H
    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if addr >= 0x8000:
            prg_mode = (self.control >> 2) & 0x03
            if prg_mode in (0, 1):
                # 32K mode, ignore low bit
                bank = (self.prg_bank & 0x0E)
                off = bank * 0x4000 + (addr - 0x8000)
                return self.prg[off % len(self.prg)]
            elif prg_mode == 2:
                # Fix first bank at $8000, switchable at $C000
                if addr < 0xC000:
                    return self.prg[(addr - 0x8000)]
                else:
                    bank = self.prg_bank & 0x0F
                    return self.prg[(bank * 0x4000 + (addr - 0xC000)) % len(self.prg)]
            else:
                # prg_mode == 3: switchable at $8000, fix last at $C000
                if addr < 0xC000:
                    bank = self.prg_bank & 0x0F
                    return self.prg[(bank * 0x4000 + (addr - 0x8000)) % len(self.prg)]
                else:
                    bank = self.num_prg_banks - 1
                    return self.prg[(bank * 0x4000 + (addr - 0xC000)) % len(self.prg)]
        return 0
    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF
            return
        if addr < 0x8000:
            return
        if value & 0x80:
            self.shift = 0x10
            self.control |= 0x0C
            self._apply_mirroring()
            return
        complete = self.shift & 0x01
        self.shift = ((self.shift >> 1) | ((value & 0x01) << 4)) & 0x1F
        if complete:
            reg = (addr >> 13) & 0x03  # 0=$8000, 1=$A000, 2=$C000, 3=$E000
            data = self.shift
            if reg == 0:
                self.control = data
                self._apply_mirroring()
            elif reg == 1:
                self.chr_bank0 = data
            elif reg == 2:
                self.chr_bank1 = data
            else:
                self.prg_bank = data & 0x0F
            self.shift = 0x10
    def ppu_read(self, addr):
        chr_mode = (self.control >> 4) & 0x01
        if chr_mode == 0:
            # 8K mode
            bank = self.chr_bank0 & 0x1E
            return self.chr[(bank * 0x1000 + (addr & 0x1FFF)) % len(self.chr)]
        else:
            # 4K mode
            if addr < 0x1000:
                bank = self.chr_bank0 & 0x1F
                return self.chr[(bank * 0x1000 + (addr & 0x0FFF)) % len(self.chr)]
            else:
                bank = self.chr_bank1 & 0x1F
                return self.chr[(bank * 0x1000 + (addr & 0x0FFF)) % len(self.chr)]
    def ppu_write(self, addr, value):
        if not self.chr_is_ram:
            return
        chr_mode = (self.control >> 4) & 0x01
        if chr_mode == 0:
            bank = self.chr_bank0 & 0x1E
            self.chr[(bank * 0x1000 + (addr & 0x1FFF)) % len(self.chr)] = value & 0xFF
        else:
            if addr < 0x1000:
                bank = self.chr_bank0 & 0x1F
                self.chr[(bank * 0x1000 + (addr & 0x0FFF)) % len(self.chr)] = value & 0xFF
            else:
                bank = self.chr_bank1 & 0x1F
                self.chr[(bank * 0x1000 + (addr & 0x0FFF)) % len(self.chr)] = value & 0xFF


class Mapper4(Mapper):
    # MMC3
    def __init__(self, rom):
        super().__init__(rom)
        self.bank_select = 0
        self.bank_regs = [0, 0, 0, 0, 0, 0, 0, 1]
        self.prg_mode = 0
        self.chr_mode = 0
        self.num_prg_8k = max(1, len(self.prg) // 0x2000)
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enable = False
        self.irq_pending = False

    def _prg_bank(self, slot):
        last = self.num_prg_8k - 1
        if self.prg_mode == 0:
            if slot == 0: return self.bank_regs[6] & 0x3F
            if slot == 1: return self.bank_regs[7] & 0x3F
            if slot == 2: return last - 1
            return last
        else:
            if slot == 0: return last - 1
            if slot == 1: return self.bank_regs[7] & 0x3F
            if slot == 2: return self.bank_regs[6] & 0x3F
            return last

    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if addr >= 0x8000:
            slot = (addr - 0x8000) >> 13
            offset = (addr - 0x8000) & 0x1FFF
            bank = self._prg_bank(slot)
            return self.prg[(bank * 0x2000 + offset) % len(self.prg)]
        return 0

    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF
            return
        if addr < 0x8000:
            return
        even = (addr & 1) == 0
        if addr < 0xA000:
            if even:
                self.bank_select = value
                self.prg_mode = (value >> 6) & 1
                self.chr_mode = (value >> 7) & 1
            else:
                idx = self.bank_select & 0x07
                self.bank_regs[idx] = value & 0xFF
        elif addr < 0xC000:
            if even:
                self.mirroring = MIRROR_H if (value & 1) else MIRROR_V
        elif addr < 0xE000:
            if even:
                self.irq_latch = value & 0xFF
            else:
                self.irq_counter = 0
                self.irq_reload = True
        else:
            if even:
                self.irq_enable = False
                self.irq_pending = False
            else:
                self.irq_enable = True

    def _chr_bank(self, slot):
        r = self.bank_regs
        if self.chr_mode == 0:
            if slot == 0: return r[0] & 0xFE
            if slot == 1: return (r[0] & 0xFE) | 1
            if slot == 2: return r[1] & 0xFE
            if slot == 3: return (r[1] & 0xFE) | 1
            if slot == 4: return r[2]
            if slot == 5: return r[3]
            if slot == 6: return r[4]
            return r[5]
        else:
            if slot == 0: return r[2]
            if slot == 1: return r[3]
            if slot == 2: return r[4]
            if slot == 3: return r[5]
            if slot == 4: return r[0] & 0xFE
            if slot == 5: return (r[0] & 0xFE) | 1
            if slot == 6: return r[1] & 0xFE
            return (r[1] & 0xFE) | 1

    def ppu_read(self, addr):
        addr &= 0x1FFF
        slot = addr >> 10
        offset = addr & 0x3FF
        bank = self._chr_bank(slot)
        return self.chr[(bank * 0x400 + offset) % len(self.chr)]

    def ppu_write(self, addr, value):
        if not self.chr_is_ram:
            return
        addr &= 0x1FFF
        slot = addr >> 10
        offset = addr & 0x3FF
        bank = self._chr_bank(slot)
        self.chr[(bank * 0x400 + offset) % len(self.chr)] = value & 0xFF

    def on_scanline(self):
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter = (self.irq_counter - 1) & 0xFF
        if self.irq_counter == 0 and self.irq_enable:
            self.irq_pending = True


class Mapper7(Mapper):
    # AxROM: 32KB PRG bank + single-screen mirroring select
    def __init__(self, rom):
        super().__init__(rom)
        self.bank = 0
        self.num_banks = max(1, len(self.prg) // 0x8000)
        self.mirroring = MIRROR_SL

    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if addr >= 0x8000:
            return self.prg[(self.bank * 0x8000 + (addr - 0x8000)) % len(self.prg)]
        return 0

    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF
            return
        if addr >= 0x8000:
            self.bank = (value & 0x07) % self.num_banks
            self.mirroring = MIRROR_SU if (value & 0x10) else MIRROR_SL


class Mapper11(Mapper):
    # Color Dreams
    def __init__(self, rom):
        super().__init__(rom)
        self.prg_bank = 0
        self.chr_bank = 0
        self.num_prg = max(1, len(self.prg) // 0x8000)
        self.num_chr = max(1, len(self.chr) // 0x2000)

    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if addr >= 0x8000:
            return self.prg[((self.prg_bank % self.num_prg) * 0x8000 + (addr - 0x8000)) % len(self.prg)]
        return 0

    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF
        elif addr >= 0x8000:
            self.prg_bank = value & 0x03
            self.chr_bank = (value >> 4) & 0x0F

    def ppu_read(self, addr):
        return self.chr[((self.chr_bank % self.num_chr) * 0x2000 + (addr & 0x1FFF)) % len(self.chr)]

    def ppu_write(self, addr, value):
        if self.chr_is_ram:
            self.chr[((self.chr_bank % self.num_chr) * 0x2000 + (addr & 0x1FFF)) % len(self.chr)] = value & 0xFF


class Mapper66(Mapper):
    # GxROM
    def __init__(self, rom):
        super().__init__(rom)
        self.prg_bank = 0
        self.chr_bank = 0
        self.num_prg = max(1, len(self.prg) // 0x8000)
        self.num_chr = max(1, len(self.chr) // 0x2000)

    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if addr >= 0x8000:
            return self.prg[((self.prg_bank % self.num_prg) * 0x8000 + (addr - 0x8000)) % len(self.prg)]
        return 0

    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF
        elif addr >= 0x8000:
            self.prg_bank = (value >> 4) & 0x03
            self.chr_bank = value & 0x03

    def ppu_read(self, addr):
        return self.chr[((self.chr_bank % self.num_chr) * 0x2000 + (addr & 0x1FFF)) % len(self.chr)]

    def ppu_write(self, addr, value):
        if self.chr_is_ram:
            self.chr[((self.chr_bank % self.num_chr) * 0x2000 + (addr & 0x1FFF)) % len(self.chr)] = value & 0xFF


class MapperFallback(Mapper):
    # Best-effort: map full PRG into $8000-$FFFF, ignore bank writes.
    # Lets unknown-mapper ROMs at least boot to whatever the reset vector points at.
    def __init__(self, rom):
        super().__init__(rom)
        print(f"[MewNES] Mapper {rom.mapper} not implemented — using NROM-style fallback. "
              f"Game may misbehave; report so we can add it.", file=sys.stderr)

    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000:
            return self.prg_ram[addr - 0x6000]
        if addr >= 0x8000:
            return self.prg[(addr - 0x8000) % len(self.prg)]
        return 0

    def cpu_write(self, addr, value):
        if 0x6000 <= addr < 0x8000:
            self.prg_ram[addr - 0x6000] = value & 0xFF


def create_mapper(rom):
    m = rom.mapper
    if m == 0:  return Mapper0(rom)
    if m == 1:  return Mapper1(rom)
    if m == 2:  return Mapper2(rom)
    if m == 3:  return Mapper3(rom)
    if m == 4:  return Mapper4(rom)
    if m == 7:  return Mapper7(rom)
    if m == 11: return Mapper11(rom)
    if m == 66: return Mapper66(rom)
    return MapperFallback(rom)


# ============================================================
# PPU
# ============================================================

class PPU:
    def __init__(self, bus):
        self.bus = bus
        self.mapper = None

        # Registers
        self.ctrl = 0       # $2000
        self.mask = 0       # $2001
        self.status = 0     # $2002
        self.oam_addr = 0

        # Loopy
        self.v = 0
        self.t = 0
        self.x = 0
        self.w = 0  # write toggle

        self.data_buffer = 0
        self.open_bus = 0

        # Memory
        self.nametable = bytearray(0x800)  # two 1K nametables
        self.palette = bytearray(32)
        self.oam = bytearray(256)

        # Frame state
        self.scanline = 0
        self.dot = 0
        self.frame_count = 0
        self.frame_ready = False
        self.nmi_pending = False
        self.framebuffer = bytearray(NES_WIDTH * NES_HEIGHT * 3)

        # Per-frame scroll snapshot (used by simple renderer)
        self.bg_scroll_x = 0
        self.bg_scroll_y = 0
        self.bg_nametable_select = 0
        self.bg_pattern_select = 0
        self.sp_pattern_select = 0
        self.sprite_size = 0
        self.show_bg = False
        self.show_sp = False
        self.show_bg_left = False
        self.show_sp_left = False

    def set_mapper(self, mapper):
        self.mapper = mapper

    def reset(self):
        self.ctrl = 0
        self.mask = 0
        self.status = 0
        self.oam_addr = 0
        self.v = 0
        self.t = 0
        self.x = 0
        self.w = 0
        self.data_buffer = 0
        self.scanline = 0
        self.dot = 0
        self.frame_count = 0
        self.frame_ready = False
        self.nmi_pending = False

    # --- Register interface (called from CPU bus) ---

    def reg_read(self, addr):
        a = addr & 7
        if a == 2:
            v = (self.status & 0xE0) | (self.open_bus & 0x1F)
            self.status &= 0x7F  # clear vblank
            self.w = 0
            self.open_bus = v
            return v
        if a == 4:
            v = self.oam[self.oam_addr]
            self.open_bus = v
            return v
        if a == 7:
            addr_v = self.v & 0x3FFF
            if addr_v < 0x3F00:
                v = self.data_buffer
                self.data_buffer = self._mem_read(addr_v)
            else:
                v = self._mem_read(addr_v)
                self.data_buffer = self._mem_read(addr_v - 0x1000)
            self.v = (self.v + (32 if (self.ctrl & 0x04) else 1)) & 0x7FFF
            self.open_bus = v
            return v
        return self.open_bus

    def reg_write(self, addr, value):
        value &= 0xFF
        self.open_bus = value
        a = addr & 7
        if a == 0:
            prev_nmi = self.ctrl & 0x80
            self.ctrl = value
            self.t = (self.t & 0xF3FF) | ((value & 0x03) << 10)
            self.bg_nametable_select = value & 0x03
            self.bg_pattern_select = (value >> 4) & 1
            self.sp_pattern_select = (value >> 3) & 1
            self.sprite_size = 16 if (value & 0x20) else 8
            if (value & 0x80) and not prev_nmi and (self.status & 0x80):
                self.nmi_pending = True
        elif a == 1:
            self.mask = value
            self.show_bg = bool(value & 0x08)
            self.show_sp = bool(value & 0x10)
            self.show_bg_left = bool(value & 0x02)
            self.show_sp_left = bool(value & 0x04)
        elif a == 3:
            self.oam_addr = value
        elif a == 4:
            self.oam[self.oam_addr] = value
            self.oam_addr = (self.oam_addr + 1) & 0xFF
        elif a == 5:
            if self.w == 0:
                self.t = (self.t & 0x7FE0) | (value >> 3)
                self.x = value & 0x07
                self.w = 1
            else:
                self.t = (self.t & 0x0C1F) | ((value & 0x07) << 12) | ((value & 0xF8) << 2)
                self.w = 0
        elif a == 6:
            if self.w == 0:
                self.t = (self.t & 0x00FF) | ((value & 0x3F) << 8)
                self.w = 1
            else:
                self.t = (self.t & 0x7F00) | value
                self.v = self.t
                self.w = 0
        elif a == 7:
            addr_v = self.v & 0x3FFF
            self._mem_write(addr_v, value)
            self.v = (self.v + (32 if (self.ctrl & 0x04) else 1)) & 0x7FFF

    def oam_dma_write(self, byte):
        self.oam[self.oam_addr] = byte & 0xFF
        self.oam_addr = (self.oam_addr + 1) & 0xFF

    # --- PPU bus ---

    def _nt_mirror(self, addr):
        addr = (addr - 0x2000) & 0x0FFF
        table = addr >> 10
        offset = addr & 0x03FF
        m = self.mapper.mirroring if self.mapper else MIRROR_H
        if m == MIRROR_H:
            phys = (table >> 1) * 0x400 + offset
        elif m == MIRROR_V:
            phys = (table & 1) * 0x400 + offset
        elif m == MIRROR_SL:
            phys = offset
        elif m == MIRROR_SU:
            phys = 0x400 + offset
        else:
            phys = table * 0x400 + offset
        return phys & 0x7FF

    def _mem_read(self, addr):
        addr &= 0x3FFF
        if addr < 0x2000:
            return self.mapper.ppu_read(addr) if self.mapper else 0
        if addr < 0x3F00:
            return self.nametable[self._nt_mirror(addr)]
        # Palette
        p = addr & 0x1F
        if p in (0x10, 0x14, 0x18, 0x1C):
            p -= 0x10
        return self.palette[p]

    def _mem_write(self, addr, value):
        addr &= 0x3FFF
        value &= 0xFF
        if addr < 0x2000:
            if self.mapper:
                self.mapper.ppu_write(addr, value)
            return
        if addr < 0x3F00:
            self.nametable[self._nt_mirror(addr)] = value
            return
        p = addr & 0x1F
        if p in (0x10, 0x14, 0x18, 0x1C):
            p -= 0x10
        self.palette[p] = value & 0x3F

    # --- Frame rendering ---

    def snapshot_scroll(self):
        # Take a snapshot at the start of the visible frame
        # Use the t register (next-frame scroll latch)
        coarse_x = self.t & 0x1F
        coarse_y = (self.t >> 5) & 0x1F
        fine_y = (self.t >> 12) & 0x07
        self.bg_scroll_x = coarse_x * 8 + self.x
        self.bg_scroll_y = coarse_y * 8 + fine_y
        self.bg_nametable_select = (self.t >> 10) & 0x03

    def render_frame(self):
        # Background pass
        fb = self.framebuffer
        if not self.show_bg and not self.show_sp:
            # Render backdrop color
            bg_color = self.palette[0] & 0x3F
            r, g, b = NES_PALETTE[bg_color]
            for i in range(0, len(fb), 3):
                fb[i] = r
                fb[i+1] = g
                fb[i+2] = b
            return

        # Pre-decode palette to RGB for fast lookup
        pal_idx = self.palette
        # Sprite 0 hit calc
        sprite0_y = self.oam[0]
        sprite0_tile = self.oam[1]
        sprite0_attr = self.oam[2]
        sprite0_x = self.oam[3]

        # Background nametable / pattern setup
        nt_base = self.bg_nametable_select
        bg_pt = 0x1000 if self.bg_pattern_select else 0x0000
        sp_pt = 0x1000 if self.sp_pattern_select else 0x0000

        scroll_x = self.bg_scroll_x
        scroll_y = self.bg_scroll_y

        backdrop = pal_idx[0] & 0x3F
        bd_r, bd_g, bd_b = NES_PALETTE[backdrop]

        # bg_pixel_indices[y][x] holds palette color index (or -1 if transparent)
        # but to save memory and time, build the framebuffer row-by-row.
        # We also need a per-pixel 'bg_opaque' map for sprite priority and sprite 0 hit.
        bg_opaque = bytearray(NES_WIDTH * NES_HEIGHT)

        if self.show_bg:
            # Precompute RGB triplets for every (palette_set, color_bits) combo this frame
            backdrop_idx = pal_idx[0] & 0x3F
            bd_rgb = NES_PALETTE[backdrop_idx]
            bg_rgb = [None] * 16
            for ps in range(4):
                bg_rgb[ps * 4 + 0] = bd_rgb
                for cb in range(1, 4):
                    bg_rgb[ps * 4 + cb] = NES_PALETTE[pal_idx[ps * 4 + cb] & 0x3F]
            mapper_read = self.mapper.ppu_read
            nt_mirror = self._nt_mirror
            nametable = self.nametable
            show_bg_left = self.show_bg_left

            for y in range(NES_HEIGHT):
                world_y = scroll_y + y
                tile_row_y = world_y // 8
                pix_y = world_y & 7
                nt_v = (tile_row_y // 30) & 1
                tile_y = tile_row_y % 30
                attr_base = 0x3C0 + (tile_y // 4) * 8
                row_fb = y * NES_WIDTH * 3
                row_op = y * NES_WIDTH
                x = 0
                while x < NES_WIDTH:
                    world_x = scroll_x + x
                    nt_h = (world_x // 256) & 1
                    tile_x = (world_x % 256) // 8
                    pix_x_start = world_x & 7 if x == 0 else 0
                    final_nt = (nt_base ^ ((nt_v << 1) | nt_h)) & 0x03
                    nt_base_off = 0x2000 + final_nt * 0x400
                    tile_idx = nametable[nt_mirror(nt_base_off + tile_y * 32 + tile_x)]
                    attr_byte = nametable[nt_mirror(nt_base_off + attr_base + (tile_x // 4))]
                    palette_set = (attr_byte >> (((tile_y & 2) << 1) | (tile_x & 2))) & 0x03
                    pt_addr = bg_pt + tile_idx * 16 + pix_y
                    low = mapper_read(pt_addr)
                    high = mapper_read(pt_addr + 8)
                    px = pix_x_start
                    while px < 8 and x < NES_WIDTH:
                        bit = 7 - px
                        cb = ((low >> bit) & 1) | (((high >> bit) & 1) << 1)
                        if x < 8 and not show_bg_left:
                            cb = 0
                        if cb == 0:
                            bg_opaque[row_op + x] = 0
                            r, g, b = bd_rgb
                        else:
                            bg_opaque[row_op + x] = 1
                            r, g, b = bg_rgb[palette_set * 4 + cb]
                        fb_off = row_fb + x * 3
                        fb[fb_off] = r
                        fb[fb_off + 1] = g
                        fb[fb_off + 2] = b
                        px += 1
                        x += 1
        else:
            r, g, b = bd_r, bd_g, bd_b
            for i in range(0, len(fb), 3):
                fb[i] = r
                fb[i+1] = g
                fb[i+2] = b

        # Sprite pass — back-to-front so lower-index sprites win
        if self.show_sp:
            sp_size = self.sprite_size
            # Iterate sprites in reverse so sprite 0 ends up on top
            sprite_indices = list(range(63, -1, -1))
            for si in sprite_indices:
                base = si * 4
                sy = self.oam[base]
                tile = self.oam[base + 1]
                attr = self.oam[base + 2]
                sx = self.oam[base + 3]
                if sy >= 0xEF:
                    continue
                flip_h = bool(attr & 0x40)
                flip_v = bool(attr & 0x80)
                behind = bool(attr & 0x20)
                pal_set = attr & 0x03
                for row in range(sp_size):
                    py = sy + 1 + row
                    if py >= NES_HEIGHT:
                        break
                    row_in_tile = row if not flip_v else (sp_size - 1 - row)
                    if sp_size == 8:
                        pt_base = sp_pt
                        cur_tile = tile
                        fine_row = row_in_tile
                    else:
                        pt_base = 0x1000 if (tile & 1) else 0x0000
                        if row_in_tile < 8:
                            cur_tile = tile & 0xFE
                            fine_row = row_in_tile
                        else:
                            cur_tile = (tile & 0xFE) | 1
                            fine_row = row_in_tile - 8
                    pt_addr = pt_base + cur_tile * 16 + fine_row
                    low = self.mapper.ppu_read(pt_addr) if self.mapper else 0
                    high = self.mapper.ppu_read(pt_addr + 8) if self.mapper else 0
                    for col in range(8):
                        px = sx + col
                        if px >= NES_WIDTH:
                            break
                        if px < 8 and not self.show_sp_left:
                            continue
                        bit_col = col if flip_h else (7 - col)
                        cb = ((low >> bit_col) & 1) | (((high >> bit_col) & 1) << 1)
                        if cb == 0:
                            continue
                        bg_op = bg_opaque[py * NES_WIDTH + px]
                        # Sprite 0 hit
                        if si == 0 and bg_op and px != 255 and not (self.status & 0x40):
                            self.status |= 0x40
                        if behind and bg_op:
                            continue
                        pal_off = 0x10 + pal_set * 4 + cb
                        if pal_off in (0x10, 0x14, 0x18, 0x1C):
                            pal_off -= 0x10
                        col_idx = pal_idx[pal_off] & 0x3F
                        fb_off = (py * NES_WIDTH + px) * 3
                        r, g, b = NES_PALETTE[col_idx]
                        fb[fb_off] = r
                        fb[fb_off+1] = g
                        fb[fb_off+2] = b

    def start_vblank(self):
        self.status |= 0x80  # vblank
        if self.ctrl & 0x80:
            self.nmi_pending = True

    def end_vblank(self):
        self.status &= ~0x80
        self.status &= ~0x40  # sprite 0 hit clear
        self.status &= ~0x20  # sprite overflow clear


# ============================================================
# CPU (6502 / 2A03)
# ============================================================

# Addressing modes
A_IMP = 0
A_ACC = 1
A_IMM = 2
A_ZP  = 3
A_ZPX = 4
A_ZPY = 5
A_REL = 6
A_ABS = 7
A_ABX = 8
A_ABY = 9
A_IND = 10
A_IZX = 11
A_IZY = 12

# Opcode table: (op_name, addr_mode, base_cycles, page_cross_adds_cycle)
OP = [None] * 256
def _o(code, name, mode, cycles, pc=0):
    OP[code] = (name, mode, cycles, pc)

# 0x00-0x0F
_o(0x00,'brk',A_IMP,7); _o(0x01,'ora',A_IZX,6); _o(0x02,'kil',A_IMP,2); _o(0x03,'slo',A_IZX,8)
_o(0x04,'nop',A_ZP,3);  _o(0x05,'ora',A_ZP,3);  _o(0x06,'asl',A_ZP,5);  _o(0x07,'slo',A_ZP,5)
_o(0x08,'php',A_IMP,3); _o(0x09,'ora',A_IMM,2); _o(0x0A,'aslA',A_ACC,2);_o(0x0B,'anc',A_IMM,2)
_o(0x0C,'nop',A_ABS,4); _o(0x0D,'ora',A_ABS,4); _o(0x0E,'asl',A_ABS,6); _o(0x0F,'slo',A_ABS,6)
# 0x10
_o(0x10,'bpl',A_REL,2,1);_o(0x11,'ora',A_IZY,5,1);_o(0x12,'kil',A_IMP,2);_o(0x13,'slo',A_IZY,8)
_o(0x14,'nop',A_ZPX,4); _o(0x15,'ora',A_ZPX,4); _o(0x16,'asl',A_ZPX,6); _o(0x17,'slo',A_ZPX,6)
_o(0x18,'clc',A_IMP,2); _o(0x19,'ora',A_ABY,4,1);_o(0x1A,'nop',A_IMP,2);_o(0x1B,'slo',A_ABY,7)
_o(0x1C,'nop',A_ABX,4,1);_o(0x1D,'ora',A_ABX,4,1);_o(0x1E,'asl',A_ABX,7);_o(0x1F,'slo',A_ABX,7)
# 0x20
_o(0x20,'jsr',A_ABS,6); _o(0x21,'and',A_IZX,6); _o(0x22,'kil',A_IMP,2); _o(0x23,'rla',A_IZX,8)
_o(0x24,'bit',A_ZP,3);  _o(0x25,'and',A_ZP,3);  _o(0x26,'rol',A_ZP,5);  _o(0x27,'rla',A_ZP,5)
_o(0x28,'plp',A_IMP,4); _o(0x29,'and',A_IMM,2); _o(0x2A,'rolA',A_ACC,2);_o(0x2B,'anc',A_IMM,2)
_o(0x2C,'bit',A_ABS,4); _o(0x2D,'and',A_ABS,4); _o(0x2E,'rol',A_ABS,6); _o(0x2F,'rla',A_ABS,6)
# 0x30
_o(0x30,'bmi',A_REL,2,1);_o(0x31,'and',A_IZY,5,1);_o(0x32,'kil',A_IMP,2);_o(0x33,'rla',A_IZY,8)
_o(0x34,'nop',A_ZPX,4); _o(0x35,'and',A_ZPX,4); _o(0x36,'rol',A_ZPX,6); _o(0x37,'rla',A_ZPX,6)
_o(0x38,'sec',A_IMP,2); _o(0x39,'and',A_ABY,4,1);_o(0x3A,'nop',A_IMP,2);_o(0x3B,'rla',A_ABY,7)
_o(0x3C,'nop',A_ABX,4,1);_o(0x3D,'and',A_ABX,4,1);_o(0x3E,'rol',A_ABX,7);_o(0x3F,'rla',A_ABX,7)
# 0x40
_o(0x40,'rti',A_IMP,6); _o(0x41,'eor',A_IZX,6); _o(0x42,'kil',A_IMP,2); _o(0x43,'sre',A_IZX,8)
_o(0x44,'nop',A_ZP,3);  _o(0x45,'eor',A_ZP,3);  _o(0x46,'lsr',A_ZP,5);  _o(0x47,'sre',A_ZP,5)
_o(0x48,'pha',A_IMP,3); _o(0x49,'eor',A_IMM,2); _o(0x4A,'lsrA',A_ACC,2);_o(0x4B,'alr',A_IMM,2)
_o(0x4C,'jmp',A_ABS,3); _o(0x4D,'eor',A_ABS,4); _o(0x4E,'lsr',A_ABS,6); _o(0x4F,'sre',A_ABS,6)
# 0x50
_o(0x50,'bvc',A_REL,2,1);_o(0x51,'eor',A_IZY,5,1);_o(0x52,'kil',A_IMP,2);_o(0x53,'sre',A_IZY,8)
_o(0x54,'nop',A_ZPX,4); _o(0x55,'eor',A_ZPX,4); _o(0x56,'lsr',A_ZPX,6); _o(0x57,'sre',A_ZPX,6)
_o(0x58,'cli',A_IMP,2); _o(0x59,'eor',A_ABY,4,1);_o(0x5A,'nop',A_IMP,2);_o(0x5B,'sre',A_ABY,7)
_o(0x5C,'nop',A_ABX,4,1);_o(0x5D,'eor',A_ABX,4,1);_o(0x5E,'lsr',A_ABX,7);_o(0x5F,'sre',A_ABX,7)
# 0x60
_o(0x60,'rts',A_IMP,6); _o(0x61,'adc',A_IZX,6); _o(0x62,'kil',A_IMP,2); _o(0x63,'rra',A_IZX,8)
_o(0x64,'nop',A_ZP,3);  _o(0x65,'adc',A_ZP,3);  _o(0x66,'ror',A_ZP,5);  _o(0x67,'rra',A_ZP,5)
_o(0x68,'pla',A_IMP,4); _o(0x69,'adc',A_IMM,2); _o(0x6A,'rorA',A_ACC,2);_o(0x6B,'arr',A_IMM,2)
_o(0x6C,'jmp',A_IND,5); _o(0x6D,'adc',A_ABS,4); _o(0x6E,'ror',A_ABS,6); _o(0x6F,'rra',A_ABS,6)
# 0x70
_o(0x70,'bvs',A_REL,2,1);_o(0x71,'adc',A_IZY,5,1);_o(0x72,'kil',A_IMP,2);_o(0x73,'rra',A_IZY,8)
_o(0x74,'nop',A_ZPX,4); _o(0x75,'adc',A_ZPX,4); _o(0x76,'ror',A_ZPX,6); _o(0x77,'rra',A_ZPX,6)
_o(0x78,'sei',A_IMP,2); _o(0x79,'adc',A_ABY,4,1);_o(0x7A,'nop',A_IMP,2);_o(0x7B,'rra',A_ABY,7)
_o(0x7C,'nop',A_ABX,4,1);_o(0x7D,'adc',A_ABX,4,1);_o(0x7E,'ror',A_ABX,7);_o(0x7F,'rra',A_ABX,7)
# 0x80
_o(0x80,'nop',A_IMM,2); _o(0x81,'sta',A_IZX,6); _o(0x82,'nop',A_IMM,2); _o(0x83,'sax',A_IZX,6)
_o(0x84,'sty',A_ZP,3);  _o(0x85,'sta',A_ZP,3);  _o(0x86,'stx',A_ZP,3);  _o(0x87,'sax',A_ZP,3)
_o(0x88,'dey',A_IMP,2); _o(0x89,'nop',A_IMM,2); _o(0x8A,'txa',A_IMP,2); _o(0x8B,'xaa',A_IMM,2)
_o(0x8C,'sty',A_ABS,4); _o(0x8D,'sta',A_ABS,4); _o(0x8E,'stx',A_ABS,4); _o(0x8F,'sax',A_ABS,4)
# 0x90
_o(0x90,'bcc',A_REL,2,1);_o(0x91,'sta',A_IZY,6); _o(0x92,'kil',A_IMP,2);_o(0x93,'ahx',A_IZY,6)
_o(0x94,'sty',A_ZPX,4); _o(0x95,'sta',A_ZPX,4); _o(0x96,'stx',A_ZPY,4); _o(0x97,'sax',A_ZPY,4)
_o(0x98,'tya',A_IMP,2); _o(0x99,'sta',A_ABY,5); _o(0x9A,'txs',A_IMP,2); _o(0x9B,'tas',A_ABY,5)
_o(0x9C,'shy',A_ABX,5); _o(0x9D,'sta',A_ABX,5); _o(0x9E,'shx',A_ABY,5); _o(0x9F,'ahx',A_ABY,5)
# 0xA0
_o(0xA0,'ldy',A_IMM,2); _o(0xA1,'lda',A_IZX,6); _o(0xA2,'ldx',A_IMM,2); _o(0xA3,'lax',A_IZX,6)
_o(0xA4,'ldy',A_ZP,3);  _o(0xA5,'lda',A_ZP,3);  _o(0xA6,'ldx',A_ZP,3);  _o(0xA7,'lax',A_ZP,3)
_o(0xA8,'tay',A_IMP,2); _o(0xA9,'lda',A_IMM,2); _o(0xAA,'tax',A_IMP,2); _o(0xAB,'lax',A_IMM,2)
_o(0xAC,'ldy',A_ABS,4); _o(0xAD,'lda',A_ABS,4); _o(0xAE,'ldx',A_ABS,4); _o(0xAF,'lax',A_ABS,4)
# 0xB0
_o(0xB0,'bcs',A_REL,2,1);_o(0xB1,'lda',A_IZY,5,1);_o(0xB2,'kil',A_IMP,2);_o(0xB3,'lax',A_IZY,5,1)
_o(0xB4,'ldy',A_ZPX,4); _o(0xB5,'lda',A_ZPX,4); _o(0xB6,'ldx',A_ZPY,4); _o(0xB7,'lax',A_ZPY,4)
_o(0xB8,'clv',A_IMP,2); _o(0xB9,'lda',A_ABY,4,1);_o(0xBA,'tsx',A_IMP,2);_o(0xBB,'las',A_ABY,4,1)
_o(0xBC,'ldy',A_ABX,4,1);_o(0xBD,'lda',A_ABX,4,1);_o(0xBE,'ldx',A_ABY,4,1);_o(0xBF,'lax',A_ABY,4,1)
# 0xC0
_o(0xC0,'cpy',A_IMM,2); _o(0xC1,'cmp',A_IZX,6); _o(0xC2,'nop',A_IMM,2); _o(0xC3,'dcp',A_IZX,8)
_o(0xC4,'cpy',A_ZP,3);  _o(0xC5,'cmp',A_ZP,3);  _o(0xC6,'dec',A_ZP,5);  _o(0xC7,'dcp',A_ZP,5)
_o(0xC8,'iny',A_IMP,2); _o(0xC9,'cmp',A_IMM,2); _o(0xCA,'dex',A_IMP,2); _o(0xCB,'axs',A_IMM,2)
_o(0xCC,'cpy',A_ABS,4); _o(0xCD,'cmp',A_ABS,4); _o(0xCE,'dec',A_ABS,6); _o(0xCF,'dcp',A_ABS,6)
# 0xD0
_o(0xD0,'bne',A_REL,2,1);_o(0xD1,'cmp',A_IZY,5,1);_o(0xD2,'kil',A_IMP,2);_o(0xD3,'dcp',A_IZY,8)
_o(0xD4,'nop',A_ZPX,4); _o(0xD5,'cmp',A_ZPX,4); _o(0xD6,'dec',A_ZPX,6); _o(0xD7,'dcp',A_ZPX,6)
_o(0xD8,'cld',A_IMP,2); _o(0xD9,'cmp',A_ABY,4,1);_o(0xDA,'nop',A_IMP,2);_o(0xDB,'dcp',A_ABY,7)
_o(0xDC,'nop',A_ABX,4,1);_o(0xDD,'cmp',A_ABX,4,1);_o(0xDE,'dec',A_ABX,7);_o(0xDF,'dcp',A_ABX,7)
# 0xE0
_o(0xE0,'cpx',A_IMM,2); _o(0xE1,'sbc',A_IZX,6); _o(0xE2,'nop',A_IMM,2); _o(0xE3,'isc',A_IZX,8)
_o(0xE4,'cpx',A_ZP,3);  _o(0xE5,'sbc',A_ZP,3);  _o(0xE6,'inc',A_ZP,5);  _o(0xE7,'isc',A_ZP,5)
_o(0xE8,'inx',A_IMP,2); _o(0xE9,'sbc',A_IMM,2); _o(0xEA,'nop',A_IMP,2); _o(0xEB,'sbc',A_IMM,2)
_o(0xEC,'cpx',A_ABS,4); _o(0xED,'sbc',A_ABS,4); _o(0xEE,'inc',A_ABS,6); _o(0xEF,'isc',A_ABS,6)
# 0xF0
_o(0xF0,'beq',A_REL,2,1);_o(0xF1,'sbc',A_IZY,5,1);_o(0xF2,'kil',A_IMP,2);_o(0xF3,'isc',A_IZY,8)
_o(0xF4,'nop',A_ZPX,4); _o(0xF5,'sbc',A_ZPX,4); _o(0xF6,'inc',A_ZPX,6); _o(0xF7,'isc',A_ZPX,6)
_o(0xF8,'sed',A_IMP,2); _o(0xF9,'sbc',A_ABY,4,1);_o(0xFA,'nop',A_IMP,2);_o(0xFB,'isc',A_ABY,7)
_o(0xFC,'nop',A_ABX,4,1);_o(0xFD,'sbc',A_ABX,4,1);_o(0xFE,'inc',A_ABX,7);_o(0xFF,'isc',A_ABX,7)


class CPU:
    def __init__(self, bus):
        self.bus = bus
        self.a = 0
        self.x = 0
        self.y = 0
        self.s = 0xFD
        self.p = 0x24
        self.pc = 0
        self.cycles = 0
        self.stall = 0
        self.nmi_line = False
        self.irq_line = False

    def reset(self):
        self.a = 0
        self.x = 0
        self.y = 0
        self.s = 0xFD
        self.p = 0x24
        self.pc = self._read16(0xFFFC)
        self.cycles = 7
        self.stall = 0
        self.nmi_line = False
        self.irq_line = False

    def _read(self, addr):
        return self.bus.cpu_read(addr & 0xFFFF)

    def _write(self, addr, value):
        self.bus.cpu_write(addr & 0xFFFF, value & 0xFF)

    def _read16(self, addr):
        return self._read(addr) | (self._read(addr + 1) << 8)

    def _read16_bug(self, addr):
        # 6502 indirect JMP bug: wrap within page
        lo = self._read(addr)
        hi = self._read((addr & 0xFF00) | ((addr + 1) & 0xFF))
        return lo | (hi << 8)

    def _push(self, v):
        self._write(0x100 + self.s, v & 0xFF)
        self.s = (self.s - 1) & 0xFF

    def _pop(self):
        self.s = (self.s + 1) & 0xFF
        return self._read(0x100 + self.s)

    def _set_zn(self, v):
        v &= 0xFF
        if v == 0: self.p |= F_Z
        else: self.p &= ~F_Z
        if v & 0x80: self.p |= F_N
        else: self.p &= ~F_N

    def trigger_nmi(self):
        self.nmi_line = True

    def trigger_irq(self):
        self.irq_line = True

    def _nmi(self):
        self._push(self.pc >> 8)
        self._push(self.pc & 0xFF)
        self._push((self.p & ~F_B) | F_U)
        self.p |= F_I
        self.pc = self._read16(0xFFFA)
        self.cycles += 7

    def _irq(self):
        self._push(self.pc >> 8)
        self._push(self.pc & 0xFF)
        self._push((self.p & ~F_B) | F_U)
        self.p |= F_I
        self.pc = self._read16(0xFFFE)
        self.cycles += 7

    def step(self):
        if self.stall > 0:
            self.stall -= 1
            self.cycles += 1
            return 1
        if self.nmi_line:
            self.nmi_line = False
            self._nmi()
            return 7
        if self.irq_line and not (self.p & F_I):
            self.irq_line = False
            self._irq()
            return 7

        start_cycles = self.cycles
        opcode = self._read(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        entry = OP[opcode]
        if entry is None:
            self.cycles += 2
            return 2
        name, mode, base, pc_extra = entry

        # Address resolution
        addr = 0
        operand_val = 0
        page_crossed = False
        if mode == A_IMP:
            pass
        elif mode == A_ACC:
            pass
        elif mode == A_IMM:
            addr = self.pc
            self.pc = (self.pc + 1) & 0xFFFF
        elif mode == A_ZP:
            addr = self._read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
        elif mode == A_ZPX:
            addr = (self._read(self.pc) + self.x) & 0xFF
            self.pc = (self.pc + 1) & 0xFFFF
        elif mode == A_ZPY:
            addr = (self._read(self.pc) + self.y) & 0xFF
            self.pc = (self.pc + 1) & 0xFFFF
        elif mode == A_REL:
            offset = self._read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if offset & 0x80:
                offset -= 0x100
            addr = (self.pc + offset) & 0xFFFF
        elif mode == A_ABS:
            addr = self._read16(self.pc)
            self.pc = (self.pc + 2) & 0xFFFF
        elif mode == A_ABX:
            base_addr = self._read16(self.pc)
            self.pc = (self.pc + 2) & 0xFFFF
            addr = (base_addr + self.x) & 0xFFFF
            page_crossed = (base_addr & 0xFF00) != (addr & 0xFF00)
        elif mode == A_ABY:
            base_addr = self._read16(self.pc)
            self.pc = (self.pc + 2) & 0xFFFF
            addr = (base_addr + self.y) & 0xFFFF
            page_crossed = (base_addr & 0xFF00) != (addr & 0xFF00)
        elif mode == A_IND:
            ptr = self._read16(self.pc)
            self.pc = (self.pc + 2) & 0xFFFF
            addr = self._read16_bug(ptr)
        elif mode == A_IZX:
            ptr = (self._read(self.pc) + self.x) & 0xFF
            self.pc = (self.pc + 1) & 0xFFFF
            addr = self._read(ptr) | (self._read((ptr + 1) & 0xFF) << 8)
        elif mode == A_IZY:
            ptr = self._read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            base_addr = self._read(ptr) | (self._read((ptr + 1) & 0xFF) << 8)
            addr = (base_addr + self.y) & 0xFFFF
            page_crossed = (base_addr & 0xFF00) != (addr & 0xFF00)

        self.cycles += base
        if page_crossed and pc_extra:
            self.cycles += 1

        # Dispatch operation
        op = name
        if op == 'lda':
            self.a = self._read(addr); self._set_zn(self.a)
        elif op == 'ldx':
            self.x = self._read(addr); self._set_zn(self.x)
        elif op == 'ldy':
            self.y = self._read(addr); self._set_zn(self.y)
        elif op == 'sta':
            self._write(addr, self.a)
        elif op == 'stx':
            self._write(addr, self.x)
        elif op == 'sty':
            self._write(addr, self.y)
        elif op == 'tax':
            self.x = self.a; self._set_zn(self.x)
        elif op == 'tay':
            self.y = self.a; self._set_zn(self.y)
        elif op == 'txa':
            self.a = self.x; self._set_zn(self.a)
        elif op == 'tya':
            self.a = self.y; self._set_zn(self.a)
        elif op == 'tsx':
            self.x = self.s; self._set_zn(self.x)
        elif op == 'txs':
            self.s = self.x
        elif op == 'pha':
            self._push(self.a)
        elif op == 'php':
            self._push(self.p | F_B | F_U)
        elif op == 'pla':
            self.a = self._pop(); self._set_zn(self.a)
        elif op == 'plp':
            self.p = (self._pop() & ~F_B) | F_U
        elif op == 'and':
            self.a &= self._read(addr); self._set_zn(self.a)
        elif op == 'ora':
            self.a |= self._read(addr); self._set_zn(self.a)
        elif op == 'eor':
            self.a ^= self._read(addr); self._set_zn(self.a)
        elif op == 'bit':
            v = self._read(addr)
            if (self.a & v) == 0: self.p |= F_Z
            else: self.p &= ~F_Z
            self.p = (self.p & ~(F_N | F_V)) | (v & (F_N | F_V))
        elif op == 'adc':
            v = self._read(addr)
            c = self.p & F_C
            r = self.a + v + c
            if r > 0xFF: self.p |= F_C
            else: self.p &= ~F_C
            if (~(self.a ^ v) & (self.a ^ r)) & 0x80: self.p |= F_V
            else: self.p &= ~F_V
            self.a = r & 0xFF
            self._set_zn(self.a)
        elif op == 'sbc':
            v = self._read(addr) ^ 0xFF
            c = self.p & F_C
            r = self.a + v + c
            if r > 0xFF: self.p |= F_C
            else: self.p &= ~F_C
            if (~(self.a ^ v) & (self.a ^ r)) & 0x80: self.p |= F_V
            else: self.p &= ~F_V
            self.a = r & 0xFF
            self._set_zn(self.a)
        elif op == 'cmp':
            v = self._read(addr); t = (self.a - v) & 0x1FF
            if self.a >= v: self.p |= F_C
            else: self.p &= ~F_C
            self._set_zn(t & 0xFF)
        elif op == 'cpx':
            v = self._read(addr); t = (self.x - v) & 0x1FF
            if self.x >= v: self.p |= F_C
            else: self.p &= ~F_C
            self._set_zn(t & 0xFF)
        elif op == 'cpy':
            v = self._read(addr); t = (self.y - v) & 0x1FF
            if self.y >= v: self.p |= F_C
            else: self.p &= ~F_C
            self._set_zn(t & 0xFF)
        elif op == 'inc':
            v = (self._read(addr) + 1) & 0xFF
            self._write(addr, v); self._set_zn(v)
        elif op == 'inx':
            self.x = (self.x + 1) & 0xFF; self._set_zn(self.x)
        elif op == 'iny':
            self.y = (self.y + 1) & 0xFF; self._set_zn(self.y)
        elif op == 'dec':
            v = (self._read(addr) - 1) & 0xFF
            self._write(addr, v); self._set_zn(v)
        elif op == 'dex':
            self.x = (self.x - 1) & 0xFF; self._set_zn(self.x)
        elif op == 'dey':
            self.y = (self.y - 1) & 0xFF; self._set_zn(self.y)
        elif op == 'asl':
            v = self._read(addr)
            if v & 0x80: self.p |= F_C
            else: self.p &= ~F_C
            v = (v << 1) & 0xFF
            self._write(addr, v); self._set_zn(v)
        elif op == 'aslA':
            if self.a & 0x80: self.p |= F_C
            else: self.p &= ~F_C
            self.a = (self.a << 1) & 0xFF
            self._set_zn(self.a)
        elif op == 'lsr':
            v = self._read(addr)
            if v & 0x01: self.p |= F_C
            else: self.p &= ~F_C
            v >>= 1
            self._write(addr, v); self._set_zn(v)
        elif op == 'lsrA':
            if self.a & 0x01: self.p |= F_C
            else: self.p &= ~F_C
            self.a >>= 1
            self._set_zn(self.a)
        elif op == 'rol':
            v = self._read(addr)
            c = 1 if (self.p & F_C) else 0
            if v & 0x80: self.p |= F_C
            else: self.p &= ~F_C
            v = ((v << 1) | c) & 0xFF
            self._write(addr, v); self._set_zn(v)
        elif op == 'rolA':
            c = 1 if (self.p & F_C) else 0
            if self.a & 0x80: self.p |= F_C
            else: self.p &= ~F_C
            self.a = ((self.a << 1) | c) & 0xFF
            self._set_zn(self.a)
        elif op == 'ror':
            v = self._read(addr)
            c = 0x80 if (self.p & F_C) else 0
            if v & 0x01: self.p |= F_C
            else: self.p &= ~F_C
            v = ((v >> 1) | c) & 0xFF
            self._write(addr, v); self._set_zn(v)
        elif op == 'rorA':
            c = 0x80 if (self.p & F_C) else 0
            if self.a & 0x01: self.p |= F_C
            else: self.p &= ~F_C
            self.a = ((self.a >> 1) | c) & 0xFF
            self._set_zn(self.a)
        elif op == 'jmp':
            self.pc = addr
        elif op == 'jsr':
            ret = (self.pc - 1) & 0xFFFF
            self._push(ret >> 8); self._push(ret & 0xFF)
            self.pc = addr
        elif op == 'rts':
            lo = self._pop(); hi = self._pop()
            self.pc = ((hi << 8) | lo) + 1 & 0xFFFF
        elif op == 'rti':
            self.p = (self._pop() & ~F_B) | F_U
            lo = self._pop(); hi = self._pop()
            self.pc = (hi << 8) | lo
        elif op == 'brk':
            self.pc = (self.pc + 1) & 0xFFFF
            self._push(self.pc >> 8); self._push(self.pc & 0xFF)
            self._push(self.p | F_B | F_U)
            self.p |= F_I
            self.pc = self._read16(0xFFFE)
        elif op == 'bpl':
            if not (self.p & F_N):
                if (self.pc & 0xFF00) != (addr & 0xFF00): self.cycles += 1
                self.cycles += 1; self.pc = addr
        elif op == 'bmi':
            if (self.p & F_N):
                if (self.pc & 0xFF00) != (addr & 0xFF00): self.cycles += 1
                self.cycles += 1; self.pc = addr
        elif op == 'bvc':
            if not (self.p & F_V):
                if (self.pc & 0xFF00) != (addr & 0xFF00): self.cycles += 1
                self.cycles += 1; self.pc = addr
        elif op == 'bvs':
            if (self.p & F_V):
                if (self.pc & 0xFF00) != (addr & 0xFF00): self.cycles += 1
                self.cycles += 1; self.pc = addr
        elif op == 'bcc':
            if not (self.p & F_C):
                if (self.pc & 0xFF00) != (addr & 0xFF00): self.cycles += 1
                self.cycles += 1; self.pc = addr
        elif op == 'bcs':
            if (self.p & F_C):
                if (self.pc & 0xFF00) != (addr & 0xFF00): self.cycles += 1
                self.cycles += 1; self.pc = addr
        elif op == 'bne':
            if not (self.p & F_Z):
                if (self.pc & 0xFF00) != (addr & 0xFF00): self.cycles += 1
                self.cycles += 1; self.pc = addr
        elif op == 'beq':
            if (self.p & F_Z):
                if (self.pc & 0xFF00) != (addr & 0xFF00): self.cycles += 1
                self.cycles += 1; self.pc = addr
        elif op == 'clc':
            self.p &= ~F_C
        elif op == 'sec':
            self.p |= F_C
        elif op == 'cli':
            self.p &= ~F_I
        elif op == 'sei':
            self.p |= F_I
        elif op == 'clv':
            self.p &= ~F_V
        elif op == 'cld':
            self.p &= ~F_D
        elif op == 'sed':
            self.p |= F_D
        elif op == 'nop':
            pass
        # Unofficial
        elif op == 'lax':
            v = self._read(addr); self.a = v; self.x = v; self._set_zn(v)
        elif op == 'sax':
            self._write(addr, self.a & self.x)
        elif op == 'dcp':
            v = (self._read(addr) - 1) & 0xFF
            self._write(addr, v)
            t = (self.a - v) & 0x1FF
            if self.a >= v: self.p |= F_C
            else: self.p &= ~F_C
            self._set_zn(t & 0xFF)
        elif op == 'isc':
            v = (self._read(addr) + 1) & 0xFF
            self._write(addr, v)
            v ^= 0xFF
            c = self.p & F_C
            r = self.a + v + c
            if r > 0xFF: self.p |= F_C
            else: self.p &= ~F_C
            if (~(self.a ^ v) & (self.a ^ r)) & 0x80: self.p |= F_V
            else: self.p &= ~F_V
            self.a = r & 0xFF
            self._set_zn(self.a)
        elif op == 'slo':
            v = self._read(addr)
            if v & 0x80: self.p |= F_C
            else: self.p &= ~F_C
            v = (v << 1) & 0xFF
            self._write(addr, v)
            self.a |= v; self._set_zn(self.a)
        elif op == 'rla':
            v = self._read(addr)
            c = 1 if (self.p & F_C) else 0
            if v & 0x80: self.p |= F_C
            else: self.p &= ~F_C
            v = ((v << 1) | c) & 0xFF
            self._write(addr, v)
            self.a &= v; self._set_zn(self.a)
        elif op == 'sre':
            v = self._read(addr)
            if v & 0x01: self.p |= F_C
            else: self.p &= ~F_C
            v >>= 1
            self._write(addr, v)
            self.a ^= v; self._set_zn(self.a)
        elif op == 'rra':
            v = self._read(addr)
            c = 0x80 if (self.p & F_C) else 0
            if v & 0x01: self.p |= F_C
            else: self.p &= ~F_C
            v = ((v >> 1) | c) & 0xFF
            self._write(addr, v)
            cin = self.p & F_C
            r = self.a + v + cin
            if r > 0xFF: self.p |= F_C
            else: self.p &= ~F_C
            if (~(self.a ^ v) & (self.a ^ r)) & 0x80: self.p |= F_V
            else: self.p &= ~F_V
            self.a = r & 0xFF
            self._set_zn(self.a)
        elif op == 'anc':
            self.a &= self._read(addr); self._set_zn(self.a)
            if self.a & 0x80: self.p |= F_C
            else: self.p &= ~F_C
        elif op == 'alr':
            self.a &= self._read(addr)
            if self.a & 0x01: self.p |= F_C
            else: self.p &= ~F_C
            self.a >>= 1; self._set_zn(self.a)
        elif op == 'arr':
            self.a &= self._read(addr)
            c = 0x80 if (self.p & F_C) else 0
            self.a = ((self.a >> 1) | c) & 0xFF
            self._set_zn(self.a)
            if self.a & 0x40: self.p |= F_C
            else: self.p &= ~F_C
            if ((self.a >> 6) ^ (self.a >> 5)) & 1: self.p |= F_V
            else: self.p &= ~F_V
        elif op == 'axs':
            v = self._read(addr)
            t = (self.a & self.x) - v
            if t >= 0: self.p |= F_C
            else: self.p &= ~F_C
            self.x = t & 0xFF; self._set_zn(self.x)
        elif op in ('xaa','tas','las','shx','shy','ahx','kil'):
            # Rarely used; treat as NOP to avoid hanging
            pass
        else:
            pass

        return self.cycles - start_cycles


# ============================================================
# Bus (system)
# ============================================================

class Bus:
    def __init__(self, rom):
        self.rom = rom
        self.mapper = create_mapper(rom)
        self.ram = bytearray(0x800)
        self.ppu = PPU(self)
        self.ppu.set_mapper(self.mapper)
        self.cpu = CPU(self)
        self.controller1 = 0
        self.controller2 = 0
        self._c1_shift = 0
        self._c2_shift = 0
        self._strobe = 0
        self.cycles_per_frame = 29780  # NTSC CPU cycles per frame
        self.cycles_at_frame_start = 0

    def reset(self):
        self.ppu.reset()
        self.cpu.reset()
        if self.mapper:
            self.mapper.reset()

    def cpu_read(self, addr):
        addr &= 0xFFFF
        if addr < 0x2000:
            return self.ram[addr & 0x7FF]
        if addr < 0x4000:
            return self.ppu.reg_read(addr)
        if addr == 0x4016:
            v = self._c1_shift & 1
            self._c1_shift = (self._c1_shift >> 1) | 0x80
            return v | 0x40
        if addr == 0x4017:
            v = self._c2_shift & 1
            self._c2_shift = (self._c2_shift >> 1) | 0x80
            return v | 0x40
        if addr < 0x4020:
            return 0
        return self.mapper.cpu_read(addr)

    def cpu_write(self, addr, value):
        addr &= 0xFFFF
        value &= 0xFF
        if addr < 0x2000:
            self.ram[addr & 0x7FF] = value
            return
        if addr < 0x4000:
            self.ppu.reg_write(addr, value)
            return
        if addr == 0x4014:
            # OAM DMA
            base = value << 8
            for i in range(256):
                self.ppu.oam_dma_write(self.cpu_read(base + i))
            self.cpu.stall += 513
            return
        if addr == 0x4016:
            self._strobe = value & 1
            if self._strobe:
                self._c1_shift = self.controller1 & 0xFF
                self._c2_shift = self.controller2 & 0xFF
            return
        if addr == 0x4017:
            return  # frame counter (APU) — ignored
        if addr < 0x4020:
            return
        self.mapper.cpu_write(addr, value)

    def run_frame(self):
        self.ppu.snapshot_scroll()
        sprite0_hit_at = -1
        s0_y = self.ppu.oam[0]
        if self.ppu.show_bg and self.ppu.show_sp and s0_y < 240:
            sprite0_hit_at = self.cpu.cycles + (s0_y + 1) * 113

        cpu = self.cpu
        ppu = self.ppu
        mapper = self.mapper

        # Visible scanlines (0..239): tick mapper IRQ counter when rendering is on
        next_sl_cycle = cpu.cycles + 113
        sl = 0
        target_vblank = cpu.cycles + 27393  # ~241 * 113.67
        while cpu.cycles < target_vblank:
            cpu.step()
            if sprite0_hit_at >= 0 and cpu.cycles >= sprite0_hit_at:
                ppu.status |= 0x40
                sprite0_hit_at = -1
            if sl < 240 and cpu.cycles >= next_sl_cycle:
                sl += 1
                next_sl_cycle += 113
                if ppu.show_bg or ppu.show_sp:
                    mapper.on_scanline()
                    if mapper.irq_pending:
                        cpu.trigger_irq()

        ppu.render_frame()
        ppu.start_vblank()
        if ppu.nmi_pending:
            cpu.trigger_nmi()
            ppu.nmi_pending = False

        # VBlank lines (~20)
        target_end = cpu.cycles + 2273
        while cpu.cycles < target_end:
            cpu.step()

        ppu.end_vblank()
        # Pre-render line
        target_end2 = cpu.cycles + 114
        while cpu.cycles < target_end2:
            cpu.step()


# ============================================================
# GUI
# ============================================================

# Default controller button bit layout (NES standard):
# bit 0: A, 1: B, 2: Select, 3: Start, 4: Up, 5: Down, 6: Left, 7: Right
KEYMAP = {
    'x': 0x01,        # A
    'z': 0x02,        # B
    'Shift_R': 0x04,  # Select
    'Return': 0x08,   # Start
    'Up': 0x10,
    'Down': 0x20,
    'Left': 0x40,
    'Right': 0x80,
}


class ACNESEmulator:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title(WINDOW_TITLE)
        self.root.configure(bg=BG)
        self.root.resizable(False, False)

        self.rom = NESROM()
        self.bus = None
        self.last_rom_dir = os.path.expanduser("~")
        self.running = True
        self.paused = False
        self.last_frame_time = time.perf_counter()
        self.fps_display = 0.0
        self.frame_count = 0
        self.fps_timer = time.perf_counter()

        self._photo = None
        self._image_id = None
        self._idle_frame = 0

        self._build_menubar()
        self._build_toolbar()
        self._build_display()
        self._build_statusbar()
        self._bind_keys()

        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self._set_status("Ready — open a ROM (File → Open ROM, Ctrl+O)")

    def _build_menubar(self):
        menubar = tk.Menu(self.root, tearoff=0, bg=BG, fg=FG,
                          activebackground="#0a246a", activeforeground="#ffffff")
        file_menu = tk.Menu(menubar, tearoff=0, bg=BG, fg=FG)
        file_menu.add_command(label="Open ROM...", accelerator="Ctrl+O", command=self.open_rom)
        file_menu.add_command(label="Close ROM", command=self.close_rom)
        file_menu.add_separator()
        file_menu.add_command(label="Save State", accelerator="F5", command=self.save_state)
        file_menu.add_command(label="Load State", accelerator="F7", command=self.load_state)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", accelerator="Alt+F4", command=self.close)
        menubar.add_cascade(label="File", menu=file_menu)

        nes_menu = tk.Menu(menubar, tearoff=0, bg=BG, fg=FG)
        nes_menu.add_command(label="Power", command=self._power)
        nes_menu.add_command(label="Reset", accelerator="F2", command=self._reset)
        nes_menu.add_separator()
        nes_menu.add_command(label="Pause", accelerator="F4", command=self._toggle_pause)
        menubar.add_cascade(label="NES", menu=nes_menu)

        help_menu = tk.Menu(menubar, tearoff=0, bg=BG, fg=FG)
        help_menu.add_command(label="Controls...", command=self._controls)
        help_menu.add_command(label="About", command=self._about)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.root.config(menu=menubar)

    def _build_toolbar(self):
        bar = tk.Frame(self.root, bg=BG, bd=1, relief=tk.RAISED)
        bar.pack(side=tk.TOP, fill=tk.X)
        for label, cmd in [("Open", self.open_rom), ("Close", self.close_rom),
                           ("|", None),
                           ("Power", self._power), ("Reset", self._reset),
                           ("|", None),
                           ("Pause", self._toggle_pause)]:
            if label == "|":
                sep = tk.Frame(bar, width=2, bg=BG_DARK, relief=tk.SUNKEN, bd=1)
                sep.pack(side=tk.LEFT, fill=tk.Y, padx=4, pady=3)
                continue
            tk.Button(bar, text=label, command=cmd, bg=BG, fg=FG,
                      relief=tk.RAISED, bd=2, padx=8, pady=1,
                      font=("Tahoma", 9)).pack(side=tk.LEFT, padx=1, pady=2)

    def _build_display(self):
        outer = tk.Frame(self.root, bg=BG, padx=8, pady=6)
        outer.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        bezel = tk.Frame(outer, bg=BG_DARK, bd=CANVAS_BORDER, relief=tk.SUNKEN)
        bezel.pack()
        self.canvas = tk.Canvas(bezel, width=NES_WIDTH * SCALE, height=NES_HEIGHT * SCALE,
                                bg="black", highlightthickness=0)
        self.canvas.pack(padx=2, pady=2)
        # Initial blank image
        self._photo = tk.PhotoImage(width=NES_WIDTH * SCALE, height=NES_HEIGHT * SCALE)
        self._image_id = self.canvas.create_image(0, 0, anchor=tk.NW, image=self._photo)

    def _build_statusbar(self):
        bar = tk.Frame(self.root, bg=BG, bd=1, relief=tk.SUNKEN)
        bar.pack(side=tk.BOTTOM, fill=tk.X)
        self.status_left = tk.Label(bar, text="", anchor=tk.W, bg=STATUS_BG, fg=FG,
                                    relief=tk.SUNKEN, bd=1, padx=6, pady=1,
                                    font=("Tahoma", 9))
        self.status_left.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2, pady=2)
        self.status_right = tk.Label(bar, text="0.0 fps", anchor=tk.E, bg=STATUS_BG, fg=FG,
                                     relief=tk.SUNKEN, bd=1, padx=6, pady=1, width=12,
                                     font=("Tahoma", 9))
        self.status_right.pack(side=tk.RIGHT, padx=2, pady=2)

    def _bind_keys(self):
        self.root.bind("<Control-o>", lambda e: self.open_rom())
        self.root.bind("<F2>", lambda e: self._reset())
        self.root.bind("<F4>", lambda e: self._toggle_pause())
        self.root.bind("<F5>", lambda e: self.save_state())
        self.root.bind("<F7>", lambda e: self.load_state())
        self.root.bind("<KeyPress>", self._on_key_press)
        self.root.bind("<KeyRelease>", self._on_key_release)

    def _on_key_press(self, ev):
        if self.bus is None:
            return
        bit = KEYMAP.get(ev.keysym)
        if bit:
            self.bus.controller1 |= bit

    def _on_key_release(self, ev):
        if self.bus is None:
            return
        bit = KEYMAP.get(ev.keysym)
        if bit:
            self.bus.controller1 &= ~bit & 0xFF

    def _set_status(self, text):
        self.status_left.config(text=text)

    def _files_disabled(self, action):
        messagebox.showinfo(action, f"{action} is disabled (FILES_OFF = True).", parent=self.root)

    def open_rom(self):
        if FILES_OFF:
            self._files_disabled("Open ROM"); return
        path = filedialog.askopenfilename(parent=self.root, title="Open NES ROM",
                                          initialdir=self.last_rom_dir, filetypes=ROM_FILTER)
        if not path:
            return
        self.last_rom_dir = os.path.dirname(path)
        ok, err = self.rom.load(path)
        if not ok:
            messagebox.showerror("Open ROM", err, parent=self.root); return
        try:
            self.bus = Bus(self.rom)
            self.bus.reset()
        except Exception as e:
            messagebox.showerror("Open ROM", f"Failed to start emulation: {e}", parent=self.root)
            self.bus = None
            return
        self.paused = False
        self.root.title(f"{self.rom.name} — {WINDOW_TITLE}")
        self._set_status(f"Running: {self.rom.info_line()}")

    def close_rom(self):
        if FILES_OFF:
            self._files_disabled("Close ROM"); return
        self.bus = None
        self.rom.close()
        self.root.title(WINDOW_TITLE)
        self._set_status("Ready — no game loaded")
        self._draw_idle()

    def _default_state_path(self):
        if not self.rom.loaded:
            return None
        base, _ = os.path.splitext(self.rom.path)
        return base + STATE_EXT

    def save_state(self):
        if FILES_OFF:
            self._files_disabled("Save State"); return
        if self.bus is None:
            messagebox.showwarning("Save State", "Load a ROM first.", parent=self.root); return
        default = self._default_state_path()
        path = filedialog.asksaveasfilename(parent=self.root, title="Save State",
                                            initialdir=os.path.dirname(default),
                                            initialfile=os.path.basename(default),
                                            defaultextension=STATE_EXT,
                                            filetypes=[("AC save state", f"*{STATE_EXT}"), ("All files", "*.*")])
        if not path:
            return
        payload = {"version": 2, "rom_path": self.rom.path, "paused": self.paused,
                   "note": "Snapshot serialization is a stub in this build."}
        with open(path, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)
        self._set_status(f"State saved (stub): {os.path.basename(path)}")

    def load_state(self):
        if FILES_OFF:
            self._files_disabled("Load State"); return
        messagebox.showinfo("Load State", "Save-state restore is not implemented in this build.", parent=self.root)

    def _controls(self):
        messagebox.showinfo("Controls",
            "Player 1:\n"
            "  D-Pad   = Arrow keys\n"
            "  A       = X\n"
            "  B       = Z\n"
            "  Start   = Enter\n"
            "  Select  = Right Shift\n\n"
            "F2 Reset   F4 Pause   Ctrl+O Open",
            parent=self.root)

    def _about(self):
        messagebox.showinfo("About",
            "AC's NES Emulator 0.2 (MewNES)\n"
            "FCEUX-style interface\n\n"
            f"PIL accelerated: {'yes' if HAS_PIL else 'no (stdlib PPM fallback)'}\n"
            f"Target: {FPS_TARGET:.4f} FPS NTSC", parent=self.root)

    def _power(self):
        if self.bus:
            self.bus.reset()
            self._set_status("Power cycle")

    def _reset(self):
        if self.bus:
            self.bus.cpu.reset()
            self._set_status("Reset")

    def _toggle_pause(self):
        self.paused = not self.paused
        if self.paused:
            self._set_status("Paused")
        elif self.rom.loaded:
            self._set_status(f"Running: {self.rom.name}")

    def close(self):
        self.running = False
        try:
            self.root.destroy()
        except tk.TclError:
            pass

    # --- Display ---

    def _blit_framebuffer(self, fb_bytes):
        if HAS_PIL:
            img = Image.frombytes('RGB', (NES_WIDTH, NES_HEIGHT), bytes(fb_bytes))
            img = img.resize((NES_WIDTH * SCALE, NES_HEIGHT * SCALE), Image.NEAREST)
            self._photo = ImageTk.PhotoImage(img)
        else:
            ppm = b"P6\n%d %d\n255\n" % (NES_WIDTH, NES_HEIGHT) + bytes(fb_bytes)
            try:
                img = tk.PhotoImage(data=ppm)
            except tk.TclError:
                # Some Tk builds don't accept raw PPM bytes; fall back to base64
                import base64
                img = tk.PhotoImage(data=base64.b64encode(ppm))
            self._photo = img.zoom(SCALE, SCALE)
        self.canvas.itemconfig(self._image_id, image=self._photo)

    def _draw_idle(self):
        # Simple animated test pattern when no ROM is loaded
        self._idle_frame += 1
        shade = (self._idle_frame * 2) % 255
        self.canvas.delete("all")
        self.canvas.create_rectangle(0, 0, NES_WIDTH * SCALE, NES_HEIGHT * SCALE,
                                     fill=f"#{shade:02x}{(80+shade//3)%255:02x}{(160+shade//5)%255:02x}",
                                     outline="")
        self.canvas.create_text(NES_WIDTH * SCALE // 2, NES_HEIGHT * SCALE // 2,
                                text="MewNES — open a ROM", fill="white",
                                font=("Tahoma", 24, "bold"))
        self._image_id = None  # invalidate; will be remade on next blit

    # --- Frame tick ---

    def tick(self):
        if not self.running:
            return
        try:
            now = time.perf_counter()
            elapsed = now - self.last_frame_time
            if elapsed >= FRAME_TIME:
                self.last_frame_time = now
                if self.bus is not None and not self.paused:
                    self.bus.run_frame()
                    if self._image_id is None:
                        # Recreate image item if we drew the idle pattern earlier
                        self._photo = tk.PhotoImage(width=NES_WIDTH * SCALE, height=NES_HEIGHT * SCALE)
                        self._image_id = self.canvas.create_image(0, 0, anchor=tk.NW, image=self._photo)
                    self._blit_framebuffer(self.bus.ppu.framebuffer)
                elif self.bus is None:
                    self._draw_idle()
                self.frame_count += 1
            if now - self.fps_timer >= 1.0:
                self.fps_display = self.frame_count / (now - self.fps_timer)
                self.frame_count = 0
                self.fps_timer = now
                self.status_right.config(text=f"{self.fps_display:.1f} fps")
        except Exception as e:
            self._set_status(f"Error: {e}")
            self.paused = True
        # Schedule next tick
        self.root.after(1, self.tick)

    def run(self):
        self.tick()
        self.root.mainloop()


if __name__ == "__main__":
    ACNESEmulator().run()
