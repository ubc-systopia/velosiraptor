pub const NUM_WORKERS: usize = 8;
pub const ITERATIONS: usize = 20;

pub struct Stats {
    pub min: u64,
    pub med: u64,
    pub avg: u64,
    pub max: u64,
    pub p99: u64,
    pub p95: u64,
    pub var: u64,
    pub std: u64,
    pub num: usize,
}

impl From<&[u64]> for Stats {
    fn from(stats: &[u64]) -> Self {
        let mut datapoints = stats.to_vec();
        datapoints.sort();
        let num_datapoints = datapoints.len();

        if num_datapoints == 0 {
            Self {
                min: 0,
                med: 0,
                avg: 0,
                max: 0,
                p99: 0,
                p95: 0,
                var: 0,
                std: 0,
                num: 0,
            }
        } else {
            // detect outliers
            let med = datapoints[num_datapoints / 2];
            let q1 = datapoints[num_datapoints / 4];
            let q3 = datapoints[num_datapoints * 3 / 4];
            let iqr = q3 - q1;
            let iqr_delta = 2* iqr; // + (iqr >> 1); // 1.5 * iqr;
            let upper_fence = q3 + iqr_delta; // q3 + 1.5 * iqr
            let lower_fence = if q1 < iqr_delta {
                0
            } else {
                q1 - iqr_delta // q1 - 1.5 * iqr
            };
            let data = if datapoints.len() > 10 {
                datapoints
                    .into_iter()
                    .filter(|x| *x <= upper_fence && *x >= lower_fence)
                    .collect::<Vec<u64>>()
            } else {
                datapoints
            };

            let num = data.len();
            let sum = data.iter().sum::<u64>() as u64;
            let avg = sum / num as u64;

            let var =
                data.iter().map(|x| (x - avg) * (x - avg)).sum::<u64>() as u64 / num as u64;
            let std = (var as f64).sqrt() as u64;
            Self {
                min: *data.first().unwrap(),
                med: data[num / 2],
                avg,
                max: *data.last().unwrap(),
                p99: data[num * 99 / 100],
                p95: data[num * 95 / 100],
                var,
                std,
                num,
            }
        }
    }
}
