// @TODO: Move the layout struct into here
pub use crate::type_infer::Layout;

pub fn align_to(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

#[derive(Clone, Copy)]
pub struct StructLayout {
    pub position: usize,
    align: usize,
}

impl StructLayout {
    pub fn new(position: usize) -> Self {
        Self {
            position,
            align: 1,
        }
    }

    pub fn new_with_align(position: usize, align: usize) -> Self {
        Self {
            position,
            align,
        }
    }

    pub fn size(&self) -> usize {
        align_to(self.position, self.align)
    }

    pub fn layout(&self) -> Layout {
        Layout {
            size: align_to(self.position, self.align),
            align: self.align,
        }
    }

    pub fn next(&mut self, field_layout: Layout) -> usize {
        self.position = align_to(self.position, field_layout.align);
        let field_pos = self.position;
        self.position += field_layout.size;
        self.align = self.align.max(field_layout.align);
        field_pos
    }
}
