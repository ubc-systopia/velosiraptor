pub const NUM_WORKERS: usize = 14;

pub struct BenchResults {
    pub tag: String,
    pub num_segments: usize,
    pub num_staticmaps: usize,
    pub num_enums: usize,
    pub num_units: usize,
    pub num_fields: usize,
    pub num_slices: usize,
    pub n_queries: Vec<usize>,
    pub n_cached: Vec<usize>,
    pub n_programs: u128,
    pub n_programs_max: Option<u128>,
}

impl BenchResults {
    pub fn new(tag: String) -> Self {
        Self {
            tag,
            num_segments: 0,
            num_staticmaps: 0,
            num_enums: 0,
            num_units: 0,
            num_fields: 0,
            num_slices: 0,
            n_programs: 0,
            n_programs_max: None,
            n_queries: Vec::new(),
            n_cached: Vec::new(),
        }
    }

    pub fn merge(&mut self, other: &Self) {
        assert_eq!(self.tag, other.tag);
        self.n_cached.extend(other.n_cached.iter());
        self.n_queries.extend(other.n_queries.iter());
        if self.num_segments == 0 {
            self.num_segments = other.num_segments;
        } else {
            assert_eq!(self.num_segments, other.num_segments);
        }
        if self.num_staticmaps == 0 {
            self.num_staticmaps = other.num_staticmaps;
        } else {
            assert_eq!(self.num_staticmaps, other.num_staticmaps);
        }
        if self.num_enums == 0 {
            self.num_enums = other.num_enums;
        } else {
            assert_eq!(self.num_enums, other.num_enums);
        }
        if self.num_units == 0 {
            self.num_units = other.num_units;
        } else {
            assert_eq!(self.num_units, other.num_units);
        }
        if self.num_fields == 0 {
            self.num_fields = other.num_fields;
        } else {
            assert_eq!(self.num_fields, other.num_fields);
        }
        if self.num_slices == 0 {
            self.num_slices = other.num_slices;
        } else {
            assert_eq!(self.num_slices, other.num_slices);
        }
        if self.n_programs == 0 {
            self.n_programs = other.n_programs;
        } else {
            assert_eq!(self.n_programs, other.n_programs);
        }
        if self.n_programs_max.is_none() {
            self.n_programs_max = other.n_programs_max;
        } else {
            assert_eq!(self.n_programs_max, other.n_programs_max);
        }
    }
}

impl std::fmt::Display for BenchResults {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:<30} {:2}U+{:2}F+{:2}S   search space: {}",
            self.tag,
            self.num_units,
            self.num_fields,
            self.num_slices,
            self.n_programs_max.unwrap_or_default()
        )?;

        Ok(())
    }
}
