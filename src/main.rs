#![allow(dead_code)]

use clap::Parser;

use image::{RgbImage, Rgb};
use std::time::Instant;

fn main() {
    let m = MandOpts::parse();

    let start = Instant::now();
    let i = make_mandelbrot(&m);
    let dur = Instant::now().duration_since(start);
    println!("took {} ms", dur.as_millis());
    i.save(&m.output).expect("shit fuck ass");
}

/// the mandelbrot
#[derive(Clone, Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct MandOpts {
    /// render width
    #[arg(short = 'W', default_value_t = 1920)]
    width: u32,
    /// render height
    #[arg(short = 'H', default_value_t = 1080)]
    height: u32,
    /// leftmost x value
    #[arg(short, default_value_t = -1.5)]
    x1: f32,
    /// lowest y value
    #[arg(short, default_value_t = 0.0)]
    y1: f32,
    /// scale
    #[arg(short, default_value_t = 2.0)]
    scale: f32,
    /// number of cycles
    #[arg(short, default_value_t = 100)]
    cycles: usize,

    /// output file name
    #[arg(short, default_value_t = String::from("output.png"))]
    output: String,

    /// algorithm choice
    #[arg(short = 'A', default_value_t = Algo::Pcheck16)]
    algorithm: Algo,

    /// enable antialiasing
    #[arg(short, default_value_t = false)]
    antialiasing: bool
}

fn make_mandelbrot(m: &MandOpts) -> RgbImage {
    RgbImage::from_fn(m.width, m.height, |x, y| {
        /*
        if x % (m.width / 16) == 0 {
            return Rgb([0, u8::MAX, 0])
        }
        if y % (m.height / 8) == 0 {
            return Rgb([0, u8::MAX, 0])
        }
        */
        
        use Algo::*;
        let algo = match m.algorithm {
            Pcheck16 => mandelbrot_16_pcheck,
            Naive => mandelbrot_no_pcheck
        };

        let y = m.height - y;
        let incr = px_to_incr(m.scale, m.width);

        if m.antialiasing {
            let points = [
                point_to_complex(x, y, m.x1, m.y1, incr),
                point_to_complex((x * 2) + 1, y * 2, m.x1, m.y1, incr / 2.0),
                point_to_complex(x * 2, (y * 2) + 2, m.x1, m.y1, incr / 2.0),
                point_to_complex((x * 2) + 1, (y * 2) + 2, m.x1, m.y1, incr / 2.0),
            ].map(|c| complex_to_colour(algo, c, m.cycles).0);
            Rgb(average_colour(&points))
        }
        else {
            let c = point_to_complex(x, y, m.x1, m.y1, incr);

            complex_to_colour(algo, c, m.cycles)
        }

        
    })
}

fn complex_to_colour<F>(f: F, c: Complex, cycles: usize) -> Rgb<u8>
where F: Fn(Complex, usize) -> MandelbrotOutcome {
    match f(c, cycles) {
        MagEscape(i) => {
            let i = i.try_into().unwrap_or(u8::MAX).saturating_mul(2);
            Rgb([i, 0, 0])
        }
        _ => Rgb([u8::MAX; 3]),
        /*Cycle(i) => {
            let i = i.try_into().unwrap_or(u8::MAX).saturating_mul(2);
            Rgb([0, i, 0])
        }*/
    }
}

fn average_colour(inputs: &[[u8; 3]]) -> [u8; 3] {
    let mut acc: [u16; 3] = [0; 3];
    for i in inputs {
        acc.iter_mut().zip(i.iter()).for_each(|(acc, src)| *acc += *src as u16)
    }
    acc.map(|c| (c / inputs.len() as u16) as u8)
}

/// x and y are pixels (float here for AA reasons)
/// x1 and y1 are the bottom left corner of the desired view
/// incr is calculated from px_to_incr
fn point_to_complex(x: u32, y: u32, x1: f32, y1: f32, incr: f32) -> Complex {
    let real = (x as f32 * incr) + x1;
    let imag = (y as f32 * incr) + y1;
    Complex { real, imag }
}

/// difference in value between two adjacent pixels
fn px_to_incr(scale: f32, width: u32) -> f32 {
    (1.0 / width as f32) * scale
}

enum MandelbrotOutcome {
    Cycle(usize),
    NoDiverge,
    MagEscape(usize),
}
use MandelbrotOutcome::*;

#[derive(Copy, Clone, clap::ValueEnum, Debug)]
enum Algo {
    Pcheck16, Naive
}
impl std::str::FromStr for Algo {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use Algo::*;
        Ok(match s {
            "pcheck16" => Pcheck16,
            "naive" => Naive,
            _ => return Err(())
        })
    }
}
impl std::fmt::Display for Algo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Algo::*;
        let s = match self {
            Pcheck16 => "pcheck16",
            Naive => "naive"
        };
        write!(f, "{}", s)
    }
}

fn mandelbrot_16_pcheck(c: Complex, limit: usize) -> MandelbrotOutcome {
    let mut z = Complex { real: 0.0, imag: 0.0 };

    let mut old = z;
    
    for i in 0..limit {
        if i % 16 == 0 {
            old = z
        }
        z = z.square() + c;
        if z.fuzzy_eq(old) {
            return Cycle(i)
        }
        let mag = z.magnitude();
        if mag > 2.0 {
            return MagEscape(i)
        }
    }
    NoDiverge
}

fn mandelbrot_no_pcheck(c: Complex, limit: usize) -> MandelbrotOutcome {
    let mut z = Complex { real: 0.0, imag: 0.0 };

    for i in 0..limit {
        z = z.square() + c;
        let mag = z.magnitude();
        if mag > 2.0 {
            return MagEscape(i)
        }
    }
    NoDiverge
}

#[derive(Clone, Copy, Debug)]
pub struct Complex {
    pub real: f32,
    pub imag: f32
}
impl Complex {
    fn square(self) -> Complex {
        let real = self.real.powi(2) - self.imag.powi(2);
        let imag = self.real * self.imag * 2.0;
        Complex { real, imag }
    }
    fn magnitude(self) -> f32 {
        (self.real.powi(2) + self.imag.powi(2)).sqrt()
    }

    fn fuzzy_eq(self, other: Self) -> bool {
        float_fuzzy_eq(self.real, other.real) && float_fuzzy_eq(self.imag, other.imag)
    }
}
impl std::ops::Add for Complex {
    type Output = Complex;
    fn add(self, rhs: Self) -> Self::Output {
        Complex {
            real: self.real + rhs.real,
            imag: self.imag + rhs.imag
        }
    }
}

fn float_fuzzy_eq(lhs: f32, rhs: f32) -> bool {
    if lhs.is_sign_positive() ^ rhs.is_sign_positive() { // different signs, can't be fuzzy-equal
        return false
    }
    else {
        let lhs_i = lhs.abs().to_bits();
        let rhs_i = rhs.abs().to_bits();
        let ulps = lhs_i.abs_diff(rhs_i);
        ulps <= 2
    }
}

