pub const NUM_WORKERS: usize = 14;
pub const ITERATIONS: usize = 500;

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
        let mut datapoints = stats.to_vec();
        datapoints.sort();
        let num_datapoints = datapoints.len();

        if num_datapoints == 0 {
            Self {
                min: 0,
                med: 0,
                avg: 0,
                max: 0,
                var: 0,
                std: 0,
                num: 0,
            }
        } else {
            // detect outliers
            let med = datapoints[num_datapoints / 2];
            let q1 = datapoints[num_datapoints / 4];
            let q3 = datapoints[num_datapoints / 4 * 3];
            let iqr = q3 - q1;
            let iqr_delta = iqr + (iqr >> 1); // 1.5 * iqr;
            let upper_fence = q3 + iqr_delta; // q3 + 1.5 * iqr
            let lower_fence = if q1 < iqr_delta {
                0
            } else {
                q1 - iqr_delta // q1 - 1.5 * iqr
            };
            let data = if datapoints.len() > 10 {
                datapoints
                    .into_iter()
                    .filter(|x| *x < upper_fence && *x > lower_fence)
                    .collect::<Vec<u128>>()
            } else {
                datapoints
            };

            let num = data.len();
            let sum = data.iter().sum::<u128>() as u128;
            let avg = sum / num as u128;

            let var =
                data.iter().map(|x| (x - avg) * (x - avg)).sum::<u128>() as u128 / num as u128;
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
}

impl From<&[usize]> for Stats {
    fn from(stats: &[usize]) -> Self {
        let data: Vec<u128> = stats.iter().map(|x| *x as u128).collect();
        Stats::from(data.as_slice())
    }
}

pub struct BenchResults {
    pub tag: String,
    pub t_parse: Vec<u128>,
    pub t_model: Vec<u128>,
    pub t_check: Vec<u128>,
    pub t_synth: Vec<u128>,
    pub t_finalize: Vec<u128>,
    pub t_total: Vec<u128>,
    pub num_segments: usize,
    pub num_staticmaps: usize,
    pub num_enums: usize,
    pub num_units: usize,
    pub num_fields: usize,
    pub num_slices: usize,
    pub map_len: usize,
    pub unmap_len: usize,
    pub protect_len: usize,
    pub n_queries: Vec<usize>,
    pub n_cached: Vec<usize>,
}

impl BenchResults {
    pub fn new(tag: String) -> Self {
        Self {
            tag,
            t_parse: Vec::new(),
            t_model: Vec::new(),
            t_check: Vec::new(),
            t_synth: Vec::new(),
            t_total: Vec::new(),
            t_finalize: Vec::new(),
            num_segments: 0,
            num_staticmaps: 0,
            num_enums: 0,
            num_units: 0,
            num_fields: 0,
            num_slices: 0,
            map_len: 0,
            unmap_len: 0,
            protect_len: 0,
            n_queries: Vec::new(),
            n_cached: Vec::new(),
        }
    }

    pub fn merge(&mut self, other: &Self) {
        assert_eq!(self.tag, other.tag);
        self.t_parse.extend(other.t_parse.iter());
        self.t_model.extend(other.t_model.iter());
        self.t_check.extend(other.t_check.iter());
        self.t_synth.extend(other.t_synth.iter());
        self.t_total.extend(other.t_total.iter());
        self.t_finalize.extend(other.t_finalize.iter());
        self.n_cached.extend(other.n_cached.iter());
        self.n_queries.extend(other.n_queries.iter());
        self.map_len = other.map_len.max(self.map_len);
        self.unmap_len = other.unmap_len.max(self.unmap_len);
        self.protect_len = other.protect_len.max(self.protect_len);
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
    }

    pub fn to_latex(&self) -> String {
        let tt = Stats::from(self.t_total.as_slice());
        format!(
            "{:<30} & {:2}U+{:2}F+{:2}S  & {:2}M+{:2}P+{:2}U & {:10}ms & (+/- {:4})\\\\\n",
            self.tag,
            self.num_units,
            self.num_fields,
            self.num_slices,
            self.map_len,
            self.protect_len,
            self.unmap_len,
            tt.med,
            tt.std
        )
    }
}

impl std::fmt::Display for BenchResults {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tt = Stats::from(self.t_total.as_slice());
        let tc = Stats::from(self.t_check.as_slice());
        let ts = Stats::from(self.t_synth.as_slice());
        let nq = Stats::from(self.n_queries.as_slice());

        write!(f, "{:<30} {:2}U+{:2}F+{:2}S  {:4}  {:2}M+{:2}P+{:2}U  {:5}q  {:10}ms/{:10}ms (+/- {:4})  synth: {:10}ms (+/- {:4})  check:  {:4}ms (+/- {:2})",
            self.tag, self.num_units, self.num_fields, self.num_slices, ts.num,
            self.map_len, self.protect_len, self.unmap_len, nq.med,
            tt.avg, tt.med, tt.std, ts.med, ts.std, tc.med, tc.std,
        )?;

        Ok(())
    }
}
