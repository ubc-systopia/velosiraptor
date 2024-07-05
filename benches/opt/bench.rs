pub const NUM_WORKERS: usize = 14;

pub struct Stats {
    pub min: u128,
    pub med: u128,
    pub avg: u128,
    pub max: u128,
    pub var: u128,
    pub std: u128,
    pub num: usize,
}

impl From<&[u128]> for Stats {
    fn from(stats: &[u128]) -> Self {
        let mut data = stats.to_vec();

        if data.is_empty() {
            return Self {
                min: 0,
                med: 0,
                avg: 0,
                max: 0,
                var: 0,
                std: 0,
                num: 0,
            };
        }

        data.sort();

        let sum = data.iter().sum::<u128>() as u128;
        let num = data.len();
        let avg = sum / num as u128;

        let var = data.iter().map(|x| (x - avg) * (x - avg)).sum::<u128>() as u128 / num as u128;
        let std = (var as f64).sqrt() as u128;
        Self {
            min: *data.first().unwrap(),
            med: data[num / 2],
            avg,
            max: *data.last().unwrap(),
            var,
            std,
            num,
        }
    }
}

impl From<&[usize]> for Stats {
    fn from(stats: &[usize]) -> Self {
        let data: Vec<u128> = stats.iter().map(|x| *x as u128).collect();
        Stats::from(data.as_slice())
    }
}

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
