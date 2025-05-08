use paste::paste;
use std::fmt;

// From https://www.nesdev.org/wiki/Status_flags
//
// 7  bit  0
// ---- ----
// NV1B DIZC
// |||| ||||
// |||| |||+- Carry
// |||| ||+-- Zero
// |||| |+--- Interrupt Disable
// |||| +---- Decimal
// |||+------ (No CPU effect; see: the B flag)
// ||+------- (No CPU effect; always pushed as 1)
// |+-------- Overflow
// +--------- Negative

pub struct CPU {
    memory: [u8; 0xFFFF],
    program_counter: u16,
    processor_status: u8,
    register_a: u8,
    register_x: u8,
    register_y: u8,
    stack_pointer: u8, // Stack is page 1 of memory (0x0100 - 0x01FF)
}

impl fmt::Display for CPU {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "PC: 0x{:04X}, Status: 0b{:08b}, A: 0x{:02X}, X: 0x{:02X}, Y: 0x{:02X}",
            self.program_counter,
            self.processor_status,
            self.register_a,
            self.register_x,
            self.register_y
        )
    }
}

impl CPU {
    const INIT_PROCESSOR_STATUS: u8 = 0b0010_0100; // The - bit is set to 1
    const INIT_STACK_POINTER: u8 = 0xFD;
    const PROGRAM_START: u16 = 0x8000;
}

impl Default for CPU {
    fn default() -> Self {
        CPU {
            memory: [0; 0xFFFF],
            processor_status: CPU::INIT_PROCESSOR_STATUS,
            program_counter: 0,
            register_a: 0,
            register_x: 0,
            register_y: 0,
            stack_pointer: CPU::INIT_STACK_POINTER,
        }
    }
}

impl CPU {
    const CARRY_FLAG: u8 = 0b0000_0001; // (C) Indicates unsigned overflow
    const ZERO_FLAG: u8 = 0b0000_0010; // (Z)
    const INTERRUPT_DISABLE_FLAG: u8 = 0b0000_0100; // (I)
    const DECIMAL_MODE_FLAG: u8 = 0b0000_1000; // (D)
    const BREAK_COMMAND_FLAG: u8 = 0b0001_0000; // (B)
    const OVERFLOW_FLAG: u8 = 0b0100_0000; // (V) Indicates signed overflow
    const NEGATIVE_FLAG: u8 = 0b1000_0000; // (N)

    fn is_flag_on(&self, mask: u8) -> bool {
        (self.processor_status & mask) != 0
    }

    fn clear_flag(&mut self, mask: u8) {
        self.processor_status &= !mask;
    }

    fn activate_flag(&mut self, mask: u8) {
        self.processor_status |= mask;
    }

    // Status

    pub fn is_carry_flag_on(&self) -> bool {
        self.is_flag_on(CPU::CARRY_FLAG)
    }

    pub fn is_zero_flag_on(&self) -> bool {
        self.is_flag_on(CPU::ZERO_FLAG)
    }

    pub fn is_interrupt_disable_flag_on(&self) -> bool {
        self.is_flag_on(CPU::INTERRUPT_DISABLE_FLAG)
    }

    pub fn is_decimal_mode_flag_on(&self) -> bool {
        self.is_flag_on(CPU::DECIMAL_MODE_FLAG)
    }

    pub fn is_break_command_flag_on(&self) -> bool {
        self.is_flag_on(CPU::BREAK_COMMAND_FLAG)
    }

    pub fn is_overflow_flag_on(&self) -> bool {
        self.is_flag_on(CPU::OVERFLOW_FLAG)
    }

    pub fn is_negative_flag_on(&self) -> bool {
        self.is_flag_on(CPU::NEGATIVE_FLAG)
    }

    // Disable

    fn clear_break_command_flag(&mut self) {
        self.clear_flag(CPU::BREAK_COMMAND_FLAG);
    }

    fn clear_carry_flag(&mut self) {
        self.clear_flag(CPU::CARRY_FLAG);
    }

    fn clear_zero_flag(&mut self) {
        self.clear_flag(CPU::ZERO_FLAG);
    }

    fn clear_interrupt_disable_flag(&mut self) {
        self.clear_flag(CPU::INTERRUPT_DISABLE_FLAG);
    }

    fn clear_decimal_mode_flag(&mut self) {
        self.clear_flag(CPU::DECIMAL_MODE_FLAG);
    }

    fn clear_overflow_flag(&mut self) {
        self.clear_flag(CPU::OVERFLOW_FLAG);
    }

    fn clear_negative_flag(&mut self) {
        self.clear_flag(CPU::NEGATIVE_FLAG);
    }

    // Enable

    fn activate_carry_flag(&mut self) {
        self.activate_flag(CPU::CARRY_FLAG);
    }

    fn activate_zero_flag(&mut self) {
        self.activate_flag(CPU::ZERO_FLAG);
    }

    fn activate_interrupt_disable_flag(&mut self) {
        self.activate_flag(CPU::INTERRUPT_DISABLE_FLAG);
    }

    fn activate_decimal_mode_flag(&mut self) {
        self.activate_flag(CPU::DECIMAL_MODE_FLAG);
    }

    fn activate_overflow_flag(&mut self) {
        self.activate_flag(CPU::OVERFLOW_FLAG);
    }

    fn activate_negative_flag(&mut self) {
        self.activate_flag(CPU::NEGATIVE_FLAG);
    }

    // Set

    fn set_carry_flag(&mut self, enable: bool) {
        if enable {
            self.activate_carry_flag();
        } else {
            self.clear_carry_flag();
        }
    }

    fn set_zero_flag(&mut self, enable: bool) {
        if enable {
            self.activate_zero_flag();
        } else {
            self.clear_zero_flag();
        }
    }

    fn set_overflow_flag(&mut self, enable: bool) {
        if enable {
            self.activate_overflow_flag();
        } else {
            self.clear_overflow_flag();
        }
    }

    fn set_negative_flag(&mut self, enable: bool) {
        if enable {
            self.activate_negative_flag();
        } else {
            self.clear_negative_flag();
        }
    }

    // Updates

    fn update_zero_flag(&mut self, result: u8) {
        self.set_zero_flag(result == 0);
    }

    fn update_negative_flag(&mut self, result: u8) {
        self.set_negative_flag(result & 0x80 != 0);
    }

    fn update_zero_and_negative_flag(&mut self, result: u8) {
        self.update_zero_flag(result);
        self.update_negative_flag(result);
    }
}

trait MemRead<A, V> {
    fn mem_read(&self, addr: A) -> V;
}

trait MemReadNext<V> {
    fn mem_read_next(&mut self) -> V;
}

trait MemWrite<A, V> {
    fn mem_write(&mut self, addr: A, value: V);
}

macro_rules! mem_read {
    ($addr_type:ident) => {
        impl MemRead<$addr_type, u8> for CPU {
            fn mem_read(&self, addr: $addr_type) -> u8 {
                self.memory[addr as usize]
            }
        }

        impl MemRead<$addr_type, u16> for CPU {
            fn mem_read(&self, addr: $addr_type) -> u16 {
                let lo = self.mem_read(addr);
                let hi = self.mem_read(addr.wrapping_add(1));
                u16::from_le_bytes([lo, hi])
            }
        }
    };
}

impl MemReadNext<u8> for CPU {
    fn mem_read_next(&mut self) -> u8 {
        let retval = self.mem_read(self.program_counter);
        self.program_counter += 1;
        retval
    }
}

impl MemReadNext<u16> for CPU {
    fn mem_read_next(&mut self) -> u16 {
        let retval = self.mem_read(self.program_counter);
        self.program_counter += 2;
        retval
    }
}

macro_rules! mem_write {
    ($addr_type:ident) => {
        impl MemWrite<$addr_type, u8> for CPU {
            fn mem_write(&mut self, addr: $addr_type, value: u8) {
                self.memory[addr as usize] = value;
            }
        }

        impl MemWrite<$addr_type, u16> for CPU {
            fn mem_write(&mut self, addr: $addr_type, value: u16) {
                let [lo, hi] = u16::to_le_bytes(value);
                self.memory[addr as usize] = lo;
                self.memory[addr.wrapping_add(1) as usize] = hi;
            }
        }
    };
}

mem_read!(u8);
mem_read!(u16);
mem_write!(u8);
mem_write!(u16);

impl CPU {
    fn get_stack_addr(&self) -> u16 {
        0x0100 | (self.stack_pointer as u16)
    }
}

trait StackPop<V> {
    fn stack_pop(&mut self) -> V;
}

trait StackPush<V> {
    fn stack_push(&mut self, value: V);
}

impl StackPop<u8> for CPU {
    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        let addr = self.get_stack_addr();
        self.memory[addr as usize]
    }
}

impl StackPop<u16> for CPU {
    fn stack_pop(&mut self) -> u16 {
        let lo = self.stack_pop();
        let hi = self.stack_pop();
        u16::from_le_bytes([lo, hi])
    }
}

impl StackPush<u8> for CPU {
    fn stack_push(&mut self, value: u8) {
        let addr = self.get_stack_addr();
        self.memory[addr as usize] = value;
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }
}

impl StackPush<u16> for CPU {
    fn stack_push(&mut self, value: u16) {
        let [lo, hi] = u16::to_le_bytes(value);
        // Push high byte first so that it is in the higher address
        self.stack_push(hi);
        self.stack_push(lo);
    }
}

impl CPU {
    fn mem_read_zeropage_x_addr_next(&mut self) -> u8 {
        let addr: u8 = self.mem_read_next();
        addr.wrapping_add(self.register_x)
    }

    fn mem_read_zeropage_y_addr_next(&mut self) -> u8 {
        let addr: u8 = self.mem_read_next();
        addr.wrapping_add(self.register_y)
    }

    fn mem_read_absolute_x_addr_next(&mut self) -> u16 {
        let addr: u16 = self.mem_read_next();
        addr.wrapping_add(self.register_x as u16)
    }

    fn mem_read_absolute_y_addr_next(&mut self) -> u16 {
        let addr: u16 = self.mem_read_next();
        addr.wrapping_add(self.register_y as u16)
    }

    fn mem_read_indirect_x_addr_next(&mut self) -> u16 {
        let addr: u8 = self.mem_read_next();
        let addr = addr.wrapping_add(self.register_x);
        let lo = self.memory[addr as usize];
        let hi = self.memory[addr.wrapping_add(1) as usize];
        u16::from_le_bytes([lo, hi])
    }

    fn mem_read_indirect_y_addr_next(&mut self) -> u16 {
        let addr: u8 = self.mem_read_next();
        let lo = self.memory[addr as usize];
        let hi = self.memory[addr.wrapping_add(1) as usize];
        let addr = u16::from_le_bytes([lo, hi]);
        addr.wrapping_add(self.register_y as u16)
    }
}

impl CPU {
    fn adc(&mut self, value: u8) {
        let carry = self.is_carry_flag_on() as u8;
        let (output, carry1) = self.register_a.overflowing_add(carry);
        let (output, carry2) = output.overflowing_add(value);
        self.set_carry_flag(carry1 || carry2);
        self.set_overflow_flag((self.register_a ^ output) & (value ^ output) & 0x80 != 0);
        self.register_a = output;
        self.update_zero_and_negative_flag(self.register_a);
    }

    fn and(&mut self, value: u8) {
        self.register_a &= value;
        self.update_zero_and_negative_flag(self.register_a);
    }

    fn asl(&mut self, value: u8) -> u8 {
        self.set_carry_flag(value & 0x80 != 0);
        let value = value << 1;
        self.update_zero_and_negative_flag(value);
        value
    }

    /*
        let reladdr: i8 = ...

        let reladdr_v1 = reladdr as u16;

        let reladdr_v2 = if reladdr & 0x80 != 0 {
            u16::from_le_bytes([reladdr, 0xFF]) // Sign-extend negative values
        } else {
            u16::from_le_bytes([reladdr, 0x00]) // Zero-extend positive values
        };

        assert_eq!(reladdr_v1, reladdr_v2);
    */

    fn bcc(&mut self, reladdr: i8) {
        if !self.is_carry_flag_on() {
            self.program_counter = self.program_counter.wrapping_add(reladdr as u16);
        }
    }

    fn bcs(&mut self, reladdr: i8) {
        if self.is_carry_flag_on() {
            self.program_counter = self.program_counter.wrapping_add(reladdr as u16);
        }
    }

    fn beq(&mut self, reladdr: i8) {
        if self.is_zero_flag_on() {
            self.program_counter = self.program_counter.wrapping_add(reladdr as u16);
        }
    }

    fn bit(&mut self, value: u8) {
        self.update_zero_flag(self.register_a & value);
        self.set_negative_flag(value & CPU::NEGATIVE_FLAG != 0);
        self.set_overflow_flag(value & CPU::OVERFLOW_FLAG != 0);
    }

    fn bmi(&mut self, reladdr: i8) {
        if self.is_negative_flag_on() {
            self.program_counter = self.program_counter.wrapping_add(reladdr as u16);
        }
    }

    fn bne(&mut self, reladdr: i8) {
        if !self.is_zero_flag_on() {
            self.program_counter = self.program_counter.wrapping_add(reladdr as u16);
        }
    }

    fn bpl(&mut self, reladdr: i8) {
        if !self.is_negative_flag_on() {
            self.program_counter = self.program_counter.wrapping_add(reladdr as u16);
        }
    }

    fn bvc(&mut self, reladdr: i8) {
        if !self.is_overflow_flag_on() {
            self.program_counter = self.program_counter.wrapping_add(reladdr as u16);
        }
    }

    fn bvs(&mut self, reladdr: i8) {
        if self.is_overflow_flag_on() {
            self.program_counter = self.program_counter.wrapping_add(reladdr as u16);
        }
    }

    fn clc(&mut self) {
        self.clear_carry_flag();
    }

    fn cld(&mut self) {
        self.clear_decimal_mode_flag();
    }

    fn cli(&mut self) {
        self.clear_interrupt_disable_flag();
    }

    fn clv(&mut self) {
        self.clear_overflow_flag();
    }

    fn cmp(&mut self, value: u8) {
        let (result, carry) = self.register_a.overflowing_sub(value);
        self.set_carry_flag(!carry);
        self.update_zero_and_negative_flag(result);
    }

    fn cpx(&mut self, value: u8) {
        let (result, carry) = self.register_x.overflowing_sub(value);
        self.set_carry_flag(!carry);
        self.update_zero_and_negative_flag(result);
    }

    fn cpy(&mut self, value: u8) {
        let (result, carry) = self.register_y.overflowing_sub(value);
        self.set_carry_flag(!carry);
        self.update_zero_and_negative_flag(result);
    }

    fn dec(&mut self, value: u8) -> u8 {
        let value = value.wrapping_sub(1);
        self.update_zero_and_negative_flag(value);
        value
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flag(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flag(self.register_y);
    }

    fn eor(&mut self, value: u8) {
        self.register_a ^= value;
        self.update_zero_and_negative_flag(self.register_a);
    }

    fn inc(&mut self, value: u8) -> u8 {
        let value = value.wrapping_add(1);
        self.update_zero_and_negative_flag(value);
        value
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flag(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flag(self.register_y);
    }

    fn jmp(&mut self, addr: u16) {
        self.program_counter = addr;
    }

    fn jsr(&mut self, addr: u16) {
        // Push PC - 1
        self.stack_push(self.program_counter.wrapping_sub(1));
        self.program_counter = addr;
    }

    fn lda(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flag(value);
    }

    fn ldx(&mut self, value: u8) {
        self.register_x = value;
        self.update_zero_and_negative_flag(value);
    }

    fn ldy(&mut self, value: u8) {
        self.register_y = value;
        self.update_zero_and_negative_flag(value);
    }

    fn lsr(&mut self, value: u8) -> u8 {
        self.set_carry_flag(value & 0x01 != 0);
        let value = value >> 1;
        self.update_zero_flag(value);
        self.clear_negative_flag(); // Sign bit is guaranteed to be zero
        value
    }

    fn nop(&self) {}

    fn ora(&mut self, value: u8) {
        self.register_a |= value;
        self.update_zero_and_negative_flag(self.register_a);
    }

    fn pha(&mut self) {
        self.stack_push(self.register_a);
    }

    fn php(&mut self) {
        let processor_status = self.processor_status;
        self.stack_push(processor_status | CPU::BREAK_COMMAND_FLAG); // See https://www.nesdev.org/wiki/Status_flags
    }

    fn pla(&mut self) {
        self.register_a = self.stack_pop();
        self.update_zero_and_negative_flag(self.register_a);
    }

    fn plp(&mut self) {
        self.processor_status = self.stack_pop();
        self.clear_break_command_flag();
    }

    fn rol(&mut self, value: u8) -> u8 {
        let new_value = (value << 1) | if self.is_carry_flag_on() { 0x01 } else { 0x00 };
        self.set_carry_flag(value & 0x80 != 0);
        self.update_zero_and_negative_flag(new_value);
        new_value
    }

    fn ror(&mut self, value: u8) -> u8 {
        let new_value = (value >> 1) | if self.is_carry_flag_on() { 0x80 } else { 0x00 };
        self.set_carry_flag(value & 0x01 != 0);
        self.update_zero_and_negative_flag(new_value);
        new_value
    }

    fn rti(&mut self) {
        self.plp();
        self.program_counter = self.stack_pop();
    }

    fn rts(&mut self) {
        self.program_counter = self.stack_pop();
        self.program_counter = self.program_counter.wrapping_add(1);
    }

    fn sbc(&mut self, value: u8) {
        //   A + (-M)     + (C - 1)
        // = A + (!M + 1) + (C - 1)  [2's complement]
        // = A + !M       + C
        self.adc(!value);
    }

    fn sec(&mut self) {
        self.activate_carry_flag();
    }

    fn sed(&mut self) {
        self.activate_decimal_mode_flag();
    }

    fn sei(&mut self) {
        self.activate_interrupt_disable_flag();
    }

    fn sta(&self) -> u8 {
        self.register_a
    }

    fn stx(&self) -> u8 {
        self.register_x
    }

    fn sty(&self) -> u8 {
        self.register_y
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flag(self.register_x);
    }

    fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_flag(self.register_y);
    }

    fn tsx(&mut self) {
        self.register_x = self.stack_pointer;
        self.update_zero_and_negative_flag(self.register_x);
    }

    fn txa(&mut self) {
        self.register_a = self.register_x;
        self.update_zero_and_negative_flag(self.register_a);
    }

    fn txs(&mut self) {
        self.stack_pointer = self.register_x;
    }

    fn tya(&mut self) {
        self.register_a = self.register_y;
        self.update_zero_and_negative_flag(self.register_a);
    }
}

macro_rules! read_immediate {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_immediate>](&mut self) {
                    let param = self.mem_read_next();
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! read_write_accumulator {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_write_accumulator>](&mut self) {
                    self.register_a = self.$name(self.register_a);
                }
            }
        }
    };
}

macro_rules! read_zeropage {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_zeropage>](&mut self) {
                    let addr: u8 = self.mem_read_next();
                    let param = self.mem_read(addr);
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! write_zeropage {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _write_zeropage>](&mut self) {
                    let addr: u8 = self.mem_read_next();
                    self.memory[addr as usize] = self.$name();
                }
            }
        }
    };
}

macro_rules! read_write_zeropage {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_write_zeropage>](&mut self) {
                    let addr: u8 = self.mem_read_next();
                    let param = self.mem_read(addr);
                    self.memory[addr as usize] = self.$name(param);
                }
            }
        }
    };
}

macro_rules! read_zeropage_x {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_zeropage_x>](&mut self) {
                    let addr = self.mem_read_zeropage_x_addr_next();
                    let param = self.mem_read(addr);
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! write_zeropage_x {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _write_zeropage_x>](&mut self) {
                    let addr = self.mem_read_zeropage_x_addr_next();
                    self.memory[addr as usize] = self.$name();
                }
            }
        }
    };
}

macro_rules! read_write_zeropage_x {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_write_zeropage_x>](&mut self) {
                    let addr = self.mem_read_zeropage_x_addr_next();
                    let param = self.mem_read(addr);
                    self.memory[addr as usize] = self.$name(param);
                }
            }
        }
    };
}

macro_rules! read_zeropage_y {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_zeropage_y>](&mut self) {
                    let addr = self.mem_read_zeropage_y_addr_next();
                    let param = self.mem_read(addr);
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! write_zeropage_y {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _write_zeropage_y>](&mut self) {
                    let addr = self.mem_read_zeropage_y_addr_next();
                    self.memory[addr as usize] = self.$name();
                }
            }
        }
    };
}

macro_rules! read_absolute {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_absolute>](&mut self) {
                    let addr: u16 = self.mem_read_next();
                    let param = self.mem_read(addr);
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! reladdr_relative {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _reladdr_relative>](&mut self) {
                    let reladdr: u8 = self.mem_read_next();
                    let reladdr = reladdr as i8;
                    self.$name(reladdr);
                }
            }
        }
    };
}

macro_rules! addr_absolute {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _addr_absolute>](&mut self) {
                    let addr: u16 = self.mem_read_next();
                    self.$name(addr);
                }
            }
        }
    };
}

macro_rules! write_absolute {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _write_absolute>](&mut self) {
                    let addr: u16 = self.mem_read_next();
                    let value = self.$name();
                    self.memory[addr as usize] = value;
                }
            }
        }
    };
}

macro_rules! read_write_absolute {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_write_absolute>](&mut self) {
                    let addr: u16 = self.mem_read_next();
                    let param = self.mem_read(addr);
                    self.memory[addr as usize] = self.$name(param);
                }
            }
        }
    };
}

macro_rules! read_absolute_x {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_absolute_x>](&mut self) {
                    let addr = self.mem_read_absolute_x_addr_next();
                    let param = self.mem_read(addr);
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! write_absolute_x {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _write_absolute_x>](&mut self) {
                    let addr = self.mem_read_absolute_x_addr_next();
                    self.memory[addr as usize] = self.$name();
                }
            }
        }
    };
}

macro_rules! read_write_absolute_x {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_write_absolute_x>](&mut self) {
                    let addr = self.mem_read_absolute_x_addr_next();
                    let param = self.mem_read(addr);
                    self.memory[addr as usize] = self.$name(param);
                }
            }
        }
    };
}

macro_rules! read_absolute_y {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_absolute_y>](&mut self) {
                    let addr = self.mem_read_absolute_y_addr_next();
                    let param = self.mem_read(addr);
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! write_absolute_y {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _write_absolute_y>](&mut self) {
                    let addr = self.mem_read_absolute_y_addr_next();
                    self.memory[addr as usize] = self.$name();
                }
            }
        }
    };
}

macro_rules! addr_indirect {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _addr_indirect>](&mut self) {
                    let addr: u16 = self.mem_read_next();
                    let lo = self.memory[addr as usize];
                    let hi = self.memory[addr.wrapping_add(1) as usize];
                    let addr = u16::from_le_bytes([lo, hi]);
                    self.$name(addr);
                }
            }
        }
    };
}

macro_rules! read_indirect_x {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_indirect_x>](&mut self) {
                    let addr = self.mem_read_indirect_x_addr_next();
                    let param = self.memory[addr as usize];
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! write_indirect_x {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _write_indirect_x>](&mut self) {
                    let addr = self.mem_read_indirect_x_addr_next();
                    self.memory[addr as usize] = self.$name();
                }
            }
        }
    };
}

macro_rules! read_indirect_y {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _read_indirect_y>](&mut self) {
                    let addr = self.mem_read_indirect_y_addr_next();
                    let param = self.memory[addr as usize];
                    self.$name(param);
                }
            }
        }
    };
}

macro_rules! write_indirect_y {
    ($name:ident) => {
        paste! {
            impl CPU {
                fn [<$name _write_indirect_y>](&mut self) {
                    let addr = self.mem_read_indirect_y_addr_next();
                    self.memory[addr as usize] = self.$name();
                }
            }
        }
    };
}

macro_rules! make_addressing_modes {
    ($func:ident, $prefix:ident, $($mode:ident),*) => {
        $(
            paste!{[<$prefix _ $mode>]!($func);}
        )*
    };
}

make_addressing_modes!(
    adc, read, immediate, zeropage, zeropage_x, absolute, absolute_x, absolute_y, indirect_x,
    indirect_y
);
make_addressing_modes!(
    and, read, immediate, zeropage, zeropage_x, absolute, absolute_x, absolute_y, indirect_x,
    indirect_y
);
make_addressing_modes!(
    asl,
    read_write,
    accumulator,
    zeropage,
    zeropage_x,
    absolute,
    absolute_x
);
make_addressing_modes!(bcc, reladdr, relative);
make_addressing_modes!(bcs, reladdr, relative);
make_addressing_modes!(beq, reladdr, relative);
make_addressing_modes!(bit, read, zeropage, absolute);
make_addressing_modes!(bmi, reladdr, relative);
make_addressing_modes!(bne, reladdr, relative);
make_addressing_modes!(bpl, reladdr, relative);
make_addressing_modes!(bvc, reladdr, relative);
make_addressing_modes!(bvs, reladdr, relative);
make_addressing_modes!(
    cmp, read, immediate, zeropage, zeropage_x, absolute, absolute_x, absolute_y, indirect_x,
    indirect_y
);
make_addressing_modes!(cpx, read, immediate, zeropage, absolute);
make_addressing_modes!(cpy, read, immediate, zeropage, absolute);
make_addressing_modes!(dec, read_write, zeropage, zeropage_x, absolute, absolute_x);
make_addressing_modes!(
    eor, read, immediate, zeropage, zeropage_x, absolute, absolute_x, absolute_y, indirect_x,
    indirect_y
);
make_addressing_modes!(inc, read_write, zeropage, zeropage_x, absolute, absolute_x);
make_addressing_modes!(jmp, addr, absolute, indirect);
make_addressing_modes!(jsr, addr, absolute);
make_addressing_modes!(
    lda, read, immediate, zeropage, zeropage_x, absolute, absolute_x, absolute_y, indirect_x,
    indirect_y
);
make_addressing_modes!(ldx, read, immediate, zeropage, zeropage_y, absolute, absolute_y);
make_addressing_modes!(ldy, read, immediate, zeropage, zeropage_x, absolute, absolute_x);
make_addressing_modes!(
    lsr,
    read_write,
    accumulator,
    zeropage,
    zeropage_x,
    absolute,
    absolute_x
);
make_addressing_modes!(
    ora, read, immediate, zeropage, zeropage_x, absolute, absolute_x, absolute_y, indirect_x,
    indirect_y
);
make_addressing_modes!(
    rol,
    read_write,
    accumulator,
    zeropage,
    zeropage_x,
    absolute,
    absolute_x
);
make_addressing_modes!(
    ror,
    read_write,
    accumulator,
    zeropage,
    zeropage_x,
    absolute,
    absolute_x
);
make_addressing_modes!(
    sbc, read, immediate, zeropage, zeropage_x, absolute, absolute_x, absolute_y, indirect_x,
    indirect_y
);
make_addressing_modes!(
    sta, write, zeropage, zeropage_x, absolute, absolute_x, absolute_y, indirect_x, indirect_y
);
make_addressing_modes!(stx, write, zeropage, zeropage_y, absolute);
make_addressing_modes!(sty, write, zeropage, zeropage_x, absolute);

macro_rules! make_run {
    ($(($name:ident, $opcode:expr)),*) => {
        impl CPU {
            fn run(&mut self) {
                loop {
                    let opcode: u8 = self.mem_read_next();
                    match opcode {
                        0x00 => break,  // BRK
                        $(
                            $opcode => self.$name(),
                        )*
                        _ => panic!("Encountered unknown opcode 0x{:02X}", opcode),
                    }
                }
            }
        }
    };
}

make_run!(
    (adc_read_immediate, 0x69),
    (adc_read_zeropage, 0x65),
    (adc_read_zeropage_x, 0x75),
    (adc_read_absolute, 0x6D),
    (adc_read_absolute_x, 0x7D),
    (adc_read_absolute_y, 0x79),
    (adc_read_indirect_x, 0x61),
    (adc_read_indirect_y, 0x71),
    (and_read_immediate, 0x29),
    (and_read_zeropage, 0x25),
    (and_read_zeropage_x, 0x35),
    (and_read_absolute, 0x2D),
    (and_read_absolute_x, 0x3D),
    (and_read_absolute_y, 0x39),
    (and_read_indirect_x, 0x21),
    (and_read_indirect_y, 0x31),
    (asl_read_write_accumulator, 0x0A),
    (asl_read_write_zeropage, 0x06),
    (asl_read_write_zeropage_x, 0x16),
    (asl_read_write_absolute, 0x0E),
    (asl_read_write_absolute_x, 0x1E),
    (bcc_reladdr_relative, 0x90),
    (bcs_reladdr_relative, 0xB0),
    (beq_reladdr_relative, 0xF0),
    (bit_read_zeropage, 0x24),
    (bit_read_absolute, 0x2C),
    (bmi_reladdr_relative, 0x30),
    (bne_reladdr_relative, 0xD0),
    (bpl_reladdr_relative, 0x10),
    (bvc_reladdr_relative, 0x50),
    (bvs_reladdr_relative, 0x70),
    (clc, 0x18),
    (cld, 0xD8),
    (cli, 0x58),
    (clv, 0xB8),
    (cmp_read_immediate, 0xC9),
    (cmp_read_zeropage, 0xC5),
    (cmp_read_zeropage_x, 0xD5),
    (cmp_read_absolute, 0xCD),
    (cmp_read_absolute_x, 0xDD),
    (cmp_read_absolute_y, 0xD9),
    (cmp_read_indirect_x, 0xC1),
    (cmp_read_indirect_y, 0xD1),
    (cpx_read_immediate, 0xE0),
    (cpx_read_zeropage, 0xE4),
    (cpx_read_absolute, 0xEC),
    (cpy_read_immediate, 0xC0),
    (cpy_read_zeropage, 0xC4),
    (cpy_read_absolute, 0xCC),
    (dec_read_write_zeropage, 0xC6),
    (dec_read_write_zeropage_x, 0xD6),
    (dec_read_write_absolute, 0xCE),
    (dec_read_write_absolute_x, 0xDE),
    (dex, 0xCA),
    (dey, 0x88),
    (eor_read_immediate, 0x49),
    (eor_read_zeropage, 0x45),
    (eor_read_zeropage_x, 0x55),
    (eor_read_absolute, 0x4D),
    (eor_read_absolute_x, 0x5D),
    (eor_read_absolute_y, 0x59),
    (eor_read_indirect_x, 0x41),
    (eor_read_indirect_y, 0x51),
    (inc_read_write_zeropage, 0xE6),
    (inc_read_write_zeropage_x, 0xF6),
    (inc_read_write_absolute, 0xEE),
    (inc_read_write_absolute_x, 0xFE),
    (inx, 0xE8),
    (iny, 0xC8),
    (jmp_addr_absolute, 0x4C),
    (jmp_addr_indirect, 0x6C),
    (jsr_addr_absolute, 0x20),
    (lda_read_immediate, 0xA9),
    (lda_read_zeropage, 0xA5),
    (lda_read_zeropage_x, 0xB5),
    (lda_read_absolute, 0xAD),
    (lda_read_absolute_x, 0xBD),
    (lda_read_absolute_y, 0xB9),
    (lda_read_indirect_x, 0xA1),
    (lda_read_indirect_y, 0xB1),
    (ldx_read_immediate, 0xA2),
    (ldx_read_zeropage, 0xA6),
    (ldx_read_zeropage_y, 0xB6),
    (ldx_read_absolute, 0xAE),
    (ldx_read_absolute_y, 0xBE),
    (ldy_read_immediate, 0xA0),
    (ldy_read_zeropage, 0xA4),
    (ldy_read_zeropage_x, 0xB4),
    (ldy_read_absolute, 0xAC),
    (ldy_read_absolute_x, 0xBC),
    (lsr_read_write_accumulator, 0x4A),
    (lsr_read_write_zeropage, 0x46),
    (lsr_read_write_zeropage_x, 0x56),
    (lsr_read_write_absolute, 0x4E),
    (lsr_read_write_absolute_x, 0x5E),
    (nop, 0xEA),
    (ora_read_immediate, 0x09),
    (ora_read_zeropage, 0x05),
    (ora_read_zeropage_x, 0x15),
    (ora_read_absolute, 0x0D),
    (ora_read_absolute_x, 0x1D),
    (ora_read_absolute_y, 0x19),
    (ora_read_indirect_x, 0x01),
    (ora_read_indirect_y, 0x11),
    (pha, 0x48),
    (php, 0x08),
    (pla, 0x68),
    (plp, 0x28),
    (rol_read_write_accumulator, 0x2A),
    (rol_read_write_zeropage, 0x26),
    (rol_read_write_zeropage_x, 0x36),
    (rol_read_write_absolute, 0x2E),
    (rol_read_write_absolute_x, 0x3E),
    (ror_read_write_accumulator, 0x6A),
    (ror_read_write_zeropage, 0x66),
    (ror_read_write_zeropage_x, 0x76),
    (ror_read_write_absolute, 0x6E),
    (ror_read_write_absolute_x, 0x7E),
    (rti, 0x40),
    (rts, 0x60),
    (sbc_read_immediate, 0xE9),
    (sbc_read_zeropage, 0xE5),
    (sbc_read_zeropage_x, 0xF5),
    (sbc_read_absolute, 0xED),
    (sbc_read_absolute_x, 0xFD),
    (sbc_read_absolute_y, 0xF9),
    (sbc_read_indirect_x, 0xE1),
    (sbc_read_indirect_y, 0xF1),
    (sec, 0x38),
    (sed, 0xF8),
    (sei, 0x78),
    (sta_write_zeropage, 0x85),
    (sta_write_zeropage_x, 0x95),
    (sta_write_absolute, 0x8D),
    (sta_write_absolute_x, 0x9D),
    (sta_write_absolute_y, 0x99),
    (sta_write_indirect_x, 0x81),
    (sta_write_indirect_y, 0x91),
    (stx_write_zeropage, 0x86),
    (stx_write_zeropage_y, 0x96),
    (stx_write_absolute, 0x8E),
    (sty_write_zeropage, 0x84),
    (sty_write_zeropage_x, 0x94),
    (sty_write_absolute, 0x8C),
    (tax, 0xAA),
    (tay, 0xA8),
    (tsx, 0xBA),
    (txa, 0x8A),
    (txs, 0x9A),
    (tya, 0x98)
);

impl CPU {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn load_and_run(&mut self, program: &[u8]) {
        self.load(program);
        self.reset();
        self.run();
    }

    fn load(&mut self, program: &[u8]) {
        let program_start = CPU::PROGRAM_START as usize;
        self.memory[program_start..(program_start + program.len())].copy_from_slice(program);
        self.mem_write(0xFFFCu16, CPU::PROGRAM_START);
    }

    fn reset(&mut self) {
        self.processor_status = CPU::INIT_PROCESSOR_STATUS;
        self.program_counter = self.mem_read(0xFFFCu16);
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.stack_pointer = CPU::INIT_STACK_POINTER;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_adc_immediate() {
        let mut cpu = CPU::new();

        cpu.load_and_run(&[
            0xA9, 0x10, // LDA #$10
            0x69, 0x05, // ADC #$05
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x15); // 0x10 + 0x05 = 0x15
        assert!(!cpu.is_carry_flag_on());
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());

        cpu.load_and_run(&[
            0x38, // SEC
            0xA9, 0xF0, // LDA #$10
            0x69, 0x0F, // ADC #$05
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x00); // 0xF0 + 0x0F + 0x01 = 0x100
        assert!(cpu.is_carry_flag_on());
        assert!(cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_and_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0xF0, // LDA #$F0
            0x29, 0x0F, // AND #$0F
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x00); // 0xF0 & 0x0F = 0x00
        assert!(cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_asl_absolute() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x40, // LDA #$40
            0x8D, 0x00, 0x20, // STA $2000
            0x0E, 0x00, 0x20, // ASL $2000
            0xAD, 0x00, 0x20, // LDA $2000
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x80); // 0x40 << 1 = 0x80
        assert!(cpu.is_negative_flag_on());
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_carry_flag_on());
    }

    #[test]
    fn test_bcc_relative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x38, // SEC
            0x90, 0x02, // BCC +2
            0xA9, 0x01, // LDA #$01
            0x18, // CLC
            0x90, 0x02, // BCC +2
            0xA9, 0x02, // LDA #$02
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x01);
    }

    #[test]
    fn test_bcs_relative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x18, // CLC
            0xB0, 0x02, // BCS +2
            0xA9, 0x01, // LDA #$01
            0x38, // SEC
            0xB0, 0x02, // BCS +2
            0xA9, 0x02, // LDA #$02
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x01);
    }

    #[test]
    fn test_beq_relative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x01, // LDA #$01
            0xC9, 0x01, // CMP #$01
            0xF0, 0x02, // BEQ +2
            0xA9, 0x02, // LDA #$02
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x01);
    }

    #[test]
    fn test_bit_zeropage() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0xF0, // LDA #$F0
            0x8D, 0x10, 0x00, // STA $0010
            0xA9, 0x0F, // LDA #$0F
            0x24, 0x10, // BIT $10
            0x00, // BRK
        ]);

        assert!(cpu.is_overflow_flag_on()); // M & 0b0100_0000 == 1
        assert!(cpu.is_negative_flag_on()); // M & 0b1000_0000 == 1
        assert!(cpu.is_zero_flag_on()); // A & M = 0
    }

    #[test]
    fn test_bmi_relative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x80, // LDA #$80
            0x30, 0x02, // BMI +2
            0xA9, 0x02, // LDA #$02
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x80);
    }

    #[test]
    fn test_bne_relative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x01, // LDA #$01
            0xD0, 0x02, // BNE +2
            0xA9, 0x00, // LDA #$00
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x01);
    }

    #[test]
    fn test_bpl_relative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x10, // LDA #$10
            0x10, 0x02, // BPL +2
            0xA9, 0x02, // LDA #$02
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x10);
    }

    #[test]
    fn test_bvc_relative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x69, 0x10, // ADC #$10
            0x50, 0x02, // BVC +2
            0xA9, 0x02, // LDA #$02
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x10);
    }

    #[test]
    fn test_bvs_relative() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x7F, // LDA #$7F
            0x69, 0x01, // ADC #$01
            0x70, 0x02, // BVS +2
            0xA9, 0x02, // LDA #$02
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x80);
    }

    #[test]
    fn test_clc_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x38, // SEC
            0x18, // CLC
            0x00, // BRK
        ]);
        assert!(!cpu.is_carry_flag_on());
    }

    #[test]
    fn test_cld_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xF8, // SED
            0xD8, // CLD
            0x00, // BRK
        ]);
        assert!(!cpu.is_decimal_mode_flag_on());
    }

    #[test]
    fn test_cli_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x78, // SEI
            0x58, // CLI
            0x00, // BRK
        ]);
        assert!(!cpu.is_interrupt_disable_flag_on());
    }

    #[test]
    fn test_clv_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x7F, // LDA #$7F
            0x69, 0x01, // ADC #$01
            0xB8, // CLV
            0x00, // BRK
        ]);
        assert!(!cpu.is_overflow_flag_on());
    }

    #[test]
    fn test_cmp_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x42, // LDA #$42
            0xC9, 0x42, // CMP #$42
            0x00, // BRK
        ]);
        assert!(cpu.is_zero_flag_on()); // A == operand
        assert!(!cpu.is_negative_flag_on()); // !(A - operand < 0)
        assert!(cpu.is_carry_flag_on()); // A >= operand
    }

    #[test]
    fn test_cpx_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x10, // LDX #$10
            0xE0, 0x08, // CPX #$08
            0x00, // BRK
        ]);
        assert!(!cpu.is_zero_flag_on()); // !(X == operand)
        assert!(!cpu.is_negative_flag_on()); // !(X - operand < 0)
        assert!(cpu.is_carry_flag_on()); // X >= operand
    }

    #[test]
    fn test_cpy_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA0, 0x05, // LDY #$05
            0xC0, 0x08, // CPY #$08
            0x00, // BRK
        ]);
        assert!(!cpu.is_zero_flag_on()); // !(Y == operand)
        assert!(cpu.is_negative_flag_on()); // Y - operand < 0
        assert!(!cpu.is_carry_flag_on()); // !(Y >= operand)
    }

    #[test]
    fn test_dec_absolute() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x02, // LDA #$02
            0x8D, 0x10, 0x00, // STA $0010
            0xCE, 0x10, 0x00, // DEC $0010
            0xAD, 0x10, 0x00, // LDA $0010
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x01);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_dex_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x00, // LDX #0
            0xCA, // DEX
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_x, 0xFF);
        assert!(cpu.is_negative_flag_on());
        assert!(!cpu.is_zero_flag_on());
    }

    #[test]
    fn test_dey_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA0, 0x02, // LDY #$02
            0x88, // DEY
            0x88, // DEY
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_y, 0x00);
        assert!(cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_eor_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x55, // LDA #$55
            0x49, 0xAA, // EOR #$AA
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0xFF);
        assert!(cpu.is_negative_flag_on());
        assert!(!cpu.is_zero_flag_on());
    }

    #[test]
    fn test_inc_zeropage() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x01, // LDA #$01
            0x8D, 0x10, 0x00, // STA $10
            0xE6, 0x10, // INC $10
            0x00, // BRK
        ]);
        assert_eq!(cpu.memory[0x10], 0x02);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_inx_implied() {
        let mut cpu = CPU::new();
        let mut program = vec![0xE8; 257]; // INX ; 257 times for overflow
        program.push(0x00); // BRK
        cpu.load_and_run(&program);
        assert_eq!(cpu.register_x, 1);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_iny_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA0, 0x01, // LDY #$01
            0xC8, // INY
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_y, 0x02);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_jmp_absolute() {
        let mut cpu = CPU::new();
        let mut program = vec![0; 4099];

        // JMP $9000
        program[0] = 0x4C;
        program[1] = 0x00;
        program[2] = 0x90;

        // BRK
        program[3] = 0x00;

        // LDA #$42
        program[4096] = 0xA9;
        program[4097] = 0x42;

        // BRK
        program[4098] = 0x00;

        cpu.load_and_run(&program);

        assert_eq!(cpu.register_a, 0x42);
    }

    #[test]
    fn test_jsr_absolute() {
        let mut cpu = CPU::new();
        let mut program: Vec<u8> = vec![0; 4099];

        // JSR $9000
        program[0] = 0x20;
        program[1] = 0x00;
        program[2] = 0x90;

        // LDX #$FF
        program[3] = 0xA2;
        program[4] = 0xFF;

        // BRK
        program[5] = 0x00;

        // LDA #$42
        program[4096] = 0xA9;
        program[4097] = 0x42;

        // RTS
        program[4098] = 0x60;

        cpu.load_and_run(&program);

        assert_eq!(cpu.register_a, 0x42);
        assert_eq!(cpu.register_x, 0xFF);
    }

    #[test]
    fn test_lda_absolute() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x42, // LDX #$42
            0x8E, 0x34, 0x12, // STX $1234
            0xAD, 0x34, 0x12, // LDA $1234
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x42);
    }

    #[test]
    fn test_lda_absolute_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x01, // LDX #$01
            0xA9, 0x42, // LDA #$42
            0x9D, 0x00, 0x20, // STA $2000,X
            0x8A, // TXA
            0xBD, 0x00, 0x20, // LDA $2000,X
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x42);
    }

    #[test]
    fn test_lda_absolute_y() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA0, 0x10, // LDY #$10
            0xA9, 0x42, // LDA #$42
            0x99, 0x00, 0x20, // STA $2000,Y
            0x98, // TYA
            0xB9, 0x00, 0x20, // LDA $2000,Y
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x42);
    }

    #[test]
    fn test_lda_immediate() {
        let mut cpu = CPU::new();
        let value = (-42i8) as u8;
        cpu.load_and_run(&[
            0xA9, value, // LDA #-42
            0x00,  // BRK
        ]);
        assert_eq!(cpu.register_a, 0b1101_0110);
        assert!(cpu.is_negative_flag_on());
        assert!(!cpu.is_zero_flag_on());
    }

    #[test]
    fn test_lda_indirect_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x04, // LDX #$04,
            0xA9, 0x10, // LDA #$10
            0x85, 0x14, // STA $14
            0xA9, 0x70, // LDA #$70
            0x85, 0x15, // STA $15
            0xA9, 0x42, // LDA #$42
            0x8D, 0x10, 0x70, // STA $7010
            0xA1, 0x10, // LDA ($10,X)
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x42);
    }

    #[test]
    fn test_lda_indirect_y() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA0, 0x04, // LDY #$04
            0xA9, 0x90, // LDA #$90
            0x85, 0x10, // STA $10
            0xA9, 0x70, // LDA #$70
            0x85, 0x11, // STA $11
            0xA9, 0x42, // LDA #$42
            0x8D, 0x94, 0x70, // STA $7094
            0xB1, 0x10, // LDA ($10),Y
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x42);
    }

    #[test]
    fn test_ldx_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x42, // LDX #$42
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_x, 0x42);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_ldy_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA0, 0x10, // LDY #$10
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_y, 0x10);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_lsr_accumulator() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x43, // LDA #$43
            0x4A, // LSR
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x21);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
        assert!(cpu.is_carry_flag_on());
    }

    #[test]
    fn test_nop_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xEA, // NOP
            0xEA, // NOP
            0x00, // BRK
        ]);
        assert_eq!(cpu.program_counter, CPU::PROGRAM_START + 3);
        assert_eq!(cpu.register_a, 0x00);
        assert_eq!(cpu.register_x, 0x00);
        assert_eq!(cpu.register_y, 0x00);
        assert_eq!(cpu.stack_pointer, CPU::INIT_STACK_POINTER);
    }

    #[test]
    fn test_ora() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x00, // LDA #$0F
            0x09, 0xFF, // ORA #$F0
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0xFF);
        assert!(!cpu.is_zero_flag_on());
        assert!(cpu.is_negative_flag_on());
    }

    #[test]
    fn test_pha_pla_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x42, // LDA #$42
            0x48, // PHA
            0xA9, 0xFF, // LDA #$FF
            0x48, // PHA
            0x68, // PLA
            0x68, // PLA
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x42);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_php_plp_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x38, // SEC
            0xF8, // SED
            0x78, // SEI
            0x08, // PHP
            0x18, // CLC
            0xD8, // CLD
            0x58, // CLI
            0x08, // PHP
            0x28, // PLP
            0x28, // PLP
            0x00, // BRK
        ]);
        assert!(cpu.is_carry_flag_on());
        assert!(cpu.is_decimal_mode_flag_on());
        assert!(cpu.is_interrupt_disable_flag_on());
    }

    #[test]
    fn test_rol_accumulator() {
        let mut cpu = CPU::new();

        cpu.load_and_run(&[
            0xA9, 0x40, // LDA #$40  ; 0b0100_0000
            0x2A, // ROL A  ; 0b1000_0000
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x80);
        assert!(!cpu.is_zero_flag_on());
        assert!(cpu.is_negative_flag_on());
        assert!(!cpu.is_carry_flag_on());

        cpu.load_and_run(&[
            0x38, // SEC
            0xA9, 0x40, // LDA #$40  ; 0b0100_0000
            0x2A, // ROL A  ; 0b1000_0001
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x81);
        assert!(!cpu.is_zero_flag_on());
        assert!(cpu.is_negative_flag_on());
        assert!(!cpu.is_carry_flag_on());
    }

    #[test]
    fn test_ror_accumulator() {
        let mut cpu = CPU::new();

        cpu.load_and_run(&[
            0xA9, 0x02, // LDA #$02  ; 0b0000_0010
            0x6A, // ROR A  ; 0b0000_0001
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x01);
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
        assert!(!cpu.is_carry_flag_on());

        cpu.load_and_run(&[
            0x38, // SEC
            0xA9, 0x02, // LDA #$02  ; 0b0000_0010
            0x6A, // ROR A  ; 0b1000_0001
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x81);
        assert!(!cpu.is_zero_flag_on());
        assert!(cpu.is_negative_flag_on());
        assert!(!cpu.is_carry_flag_on());
    }

    #[test]
    fn test_sbc_immediate() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x10, // LDA #$10
            0xE9, 0x05, // SBC #$05
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x0A); // 0x10 - 0x05 - (1 - Carry) = 0x0A
        assert!(cpu.is_carry_flag_on()); // Cleared if overflow
        assert!(!cpu.is_zero_flag_on());
        assert!(!cpu.is_negative_flag_on());
    }

    #[test]
    fn test_sec() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x38, // SEC
            0x00, // BRK
        ]);
        assert!(cpu.is_carry_flag_on());
    }

    #[test]
    fn test_sed() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xF8, // SED
            0x00, // BRK
        ]);

        assert!(cpu.is_decimal_mode_flag_on());
    }
    #[test]
    fn test_sei() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x78, // SEI
            0x00, // BRK
        ]);
        assert!(cpu.is_interrupt_disable_flag_on());
    }

    #[test]
    fn test_sta_zeropage() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x42, // LDA #$42
            0x85, 0x10, // STA $10
            0x00, // BRK
        ]);
        assert_eq!(cpu.memory[0x10], 0x42);
    }

    #[test]
    fn test_stx_zeropage_y() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x42, // LDX #$42
            0xA0, 0x05, // LDY #$05
            0x96, 0x10, // STX $10,Y
            0x00, // BRK
        ]);
        assert_eq!(cpu.memory[0x15], 0x42);
    }

    #[test]
    fn test_sty_zeropage_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA0, 0x42, // LDY #$42
            0xA2, 0x02, // LDX #$02
            0x94, 0x10, // STY $10,X
            0x00, // BRK
        ]);
        assert_eq!(cpu.memory[0x12], 0x42);
    }

    #[test]
    fn test_tax_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x42, // LDX #42
            0xAA, // TAX
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_x, 0x42);
    }

    #[test]
    fn test_tay_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA9, 0x42, // LDA #$42
            0xA8, // TAY
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_y, 0x42);
    }

    #[test]
    fn test_tsx_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0x9A, // TXS (initialize stack pointer)
            0xBA, // TSX
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_x, cpu.stack_pointer);
    }

    #[test]
    fn test_txa_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x42, // LDX #$42
            0x8A, // TXA
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x42);
    }

    #[test]
    fn test_txs_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA2, 0x42, // LDX #$42
            0x9A, // TXS
            0x00, // BRK
        ]);
        assert_eq!(cpu.stack_pointer, 0x42);
    }

    #[test]
    fn test_tya_implied() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[
            0xA0, 0x42, // LDY #$42
            0x98, // TYA
            0x00, // BRK
        ]);
        assert_eq!(cpu.register_a, 0x42);
    }
}
