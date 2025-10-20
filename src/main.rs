#![allow(dead_code)]

use itertools::Itertools;
use std::{
    cell::RefCell,
    fmt::{Display, LowerHex},
    iter::Product,
    ops::{BitAnd, BitXor, Div, Mul, Rem, Shl, Shr},
};

// type composing a polynom
type U = u64;
const ODDS: U = 0xaaaaaaaa;

const S_W: usize = U::BITS as usize;
const S: usize = 1024;
const N: usize = S / S_W;

thread_local! {
    static M: RefCell<Matrix> = RefCell::new(Matrix {
        buf: [Poly { buf: [0; N] }; S],
    });
}

/** a F_2 polynom with each bit representing the degree. */
#[derive(Debug, Eq, PartialEq, Clone, Copy, Hash)]
struct Poly {
    buf: [U; N],
}

impl Display for Poly {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} (deg. {})",
            self.buf
                .into_iter()
                .rev()
                .map(|w| format!("{:0x}", w))
                .collect::<Vec<String>>()
                .join(" "),
            self.degree()
        )
    }
}

impl LowerHex for Poly {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.buf
                .into_iter()
                .rev()
                .map(|w| format!("{:08x}", w))
                .collect::<Vec<String>>()
                .join("")
        )
    }
}
impl Poly {
    fn new(buf: [U; N]) -> Poly {
        Poly { buf }
    }
    fn zero() -> Poly {
        Poly::new([0; N])
    }

    fn one() -> Poly {
        let mut one = Poly::zero();
        one.buf[0] = 1;
        one
    }
    fn from_vec(vec: Vec<U>) -> Poly {
        let mut buf = [0; N];
        for (i, val) in vec.into_iter().enumerate() {
            buf[i] = val;
        }
        Poly { buf }
    }

    fn from_str(s: &str) -> Poly {
        let leftover = s.replace(" ", "").len() % (S_W / 4);
        let mut hex: Vec<U> = std::iter::repeat_n('0', (S_W / 4) - leftover)
            .chain(s.chars())
            .filter(|c| !c.is_whitespace())
            .chunks(S_W / 4)
            .into_iter()
            .map(|chk| chk.collect::<String>())
            .map(|s| U::from_str_radix(s.as_str(), 16).unwrap())
            .collect();

        hex.reverse();
        Poly::from_vec(hex)
    }

    fn is_zero(&self) -> bool {
        self.buf == [0; N]
    }

    fn is_one(&self) -> bool {
        if self.buf[0] != 1 {
            return false;
        };
        for i in 1..N {
            if self.buf[i] != 0 {
                return false;
            };
        }
        return true;
    }

    fn gcd(mut left: Poly, mut right: Poly) -> Poly {
        loop {
            let rem = left % right;
            if rem.is_zero() {
                return right;
            }
            left = right;
            right = rem;
        }
    }

    fn is_square(&self) -> bool {
        self.derivative().is_zero()
    }

    fn sqrt(self) -> Poly {
        let mut result = Poly::zero();
        for i in 0..(self.buf.len() / 2) {
            let b_i = i % S_W;
            let w_i = i / S_W;

            let b_2i = (2 * i) % S_W;
            let w_2i = (2 * i) / S_W;

            let val = (self.buf[w_2i] >> b_2i) & 1;

            result.buf[w_i] |= val << b_i;
        }
        result
    }

    fn derivative(mut self) -> Poly {
        // in GF2, derivative of even exposants are = 0 at modulo 2 so we void them
        let mask = ODDS;
        for i in 0..N {
            self.buf[i] &= mask;
        }

        // then bitshift right
        self >> 1
    }

    fn degree(&self) -> usize {
        for i in (0..N).rev() {
            let val = self.buf[i];
            if val > 0 {
                return val.ilog2() as usize + i * S_W;
            }
        }
        0
    }

    fn sff(self) -> Vec<(usize, Poly)> {
        let mut results = vec![];
        if self.is_zero() {
            return vec![];
        }

        let derivative = self.derivative();
        if derivative.is_zero() {
            let mut perfect_square = self;
            let mut coef = 1;
            while perfect_square.is_square() && !perfect_square.is_one() {
                coef = 2 * coef;
                perfect_square = perfect_square.sqrt();
            }
            return vec![(coef, perfect_square)];
        }
        let left = Poly::gcd(self, derivative);

        if left.is_one() {
            return vec![(1, self)];
        }

        let right = self / left;
        for factor in [left, right] {
            let sff = factor.sff();
            if !sff.is_empty() {
                results.extend(sff.into_iter().map(|(num, poly)| (num, poly)));
            }
        }
        results
    }

    fn flip_bit(&mut self, bit: usize) {
        let w_i = bit / S_W;
        let b_i = bit % S_W;

        self.buf[w_i] ^= 1 << b_i;
    }
}

impl Div<Poly> for Poly {
    type Output = Poly;

    fn div(mut self, rhs: Poly) -> Self::Output {
        let mut result = Poly::zero();
        let rhs_deg = rhs.degree();
        while self.degree() >= rhs_deg && !self.is_one() {
            let deg_diff = self.degree() - rhs_deg;
            self = self ^ (rhs << deg_diff as u32);
            result.flip_bit(deg_diff);
        }

        result
    }
}

impl Rem<Poly> for Poly {
    type Output = Poly;

    fn rem(mut self, rhs: Poly) -> Self::Output {
        let rhs_deg = rhs.degree();
        while self.degree() >= rhs_deg && !self.is_zero() {
            let deg_diff = self.degree() - rhs_deg;
            self = self ^ (rhs << deg_diff as u32);
        }

        self
    }
}

impl BitAnd<Poly> for Poly {
    type Output = Poly;
    fn bitand(mut self, rhs: Poly) -> Self::Output {
        for i in 0..N {
            self.buf[i] &= rhs.buf[i]
        }
        self
    }
}

impl BitXor<Poly> for Poly {
    type Output = Poly;
    fn bitxor(mut self, rhs: Poly) -> Self::Output {
        for i in 0..N {
            self.buf[i] ^= rhs.buf[i]
        }
        self
    }
}

impl Mul<Poly> for Poly {
    type Output = Self;
    fn mul(self, rhs: Poly) -> Self::Output {
        let mut result = Poly::zero();
        for i in 0..S {
            let word_i = i / S_W;
            let bit_i = (i % S_W) as u32;
            if (self.buf[word_i].unbounded_shr(bit_i)) & 1 > 0 {
                for j in 0..(N - word_i) {
                    let val = rhs.buf[j].unbounded_shl(bit_i);
                    let dest_j = j + word_i;
                    result.buf[dest_j] ^= val;
                }
                for j in 0..(N - word_i - 1) {
                    let val = rhs.buf[j].unbounded_shr(S_W as u32 - bit_i);
                    let dest_j = j + word_i + 1;
                    result.buf[dest_j] ^= val;
                }
            }
        }
        result
    }
}

impl Shl<u32> for Poly {
    type Output = Self;
    fn shl(mut self, rhs: u32) -> Self::Output {
        let ws = rhs as usize / S_W;
        let bs = rhs % S_W as u32;

        for i in (0..N).rev() {
            if i < ws {
                self.buf[i] = 0;
            } else {
                self.buf[i] = self.buf[i - ws].unbounded_shl(bs);
                if i > ws {
                    self.buf[i] ^= self.buf[i - ws - 1].unbounded_shr(S_W as u32 - bs);
                }
            }
        }
        self
    }
}

impl Shr<u32> for Poly {
    type Output = Self;
    fn shr(mut self, rhs: u32) -> Self::Output {
        let ws = rhs as usize / S_W;
        let bs = rhs % S_W as u32;

        for i in 0..N {
            if i + ws >= N {
                self.buf[i] = 0;
            } else {
                self.buf[i] = self.buf[i + ws].unbounded_shr(bs);
                if i + ws + 1 < N {
                    self.buf[i] ^= self.buf[i + ws + 1].unbounded_shl(S_W as u32 - bs);
                }
            }
        }
        self
    }
}

impl Ord for Poly {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for i in (0..N).rev() {
            let ord = self.buf[i].cmp(&other.buf[i]);
            if ord.is_ne() {
                return ord;
            }
        }
        std::cmp::Ordering::Equal
    }
}

impl PartialOrd for Poly {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Product for Poly {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Poly::from_vec(vec![1]), |acc, x| acc * x)
    }
}

#[derive(Eq, PartialEq)]
struct Matrix {
    buf: [Poly; S],
}

impl Matrix {
    fn new() -> Matrix {
        Matrix {
            buf: [Poly::zero(); S],
        }
    }

    fn zeroed(&mut self) {
        for i in 0..S {
            self.buf[i] = Poly::zero();
        }
    }

    fn berlekamp(&mut self, poly: Poly) {
        let size = poly.degree();
        for i in 0..size {
            self.buf[i].flip_bit(2 * i);
            self.buf[i] = self.buf[i] % poly;
            self.buf[i].flip_bit(i);
            self.buf[i] = self.buf[i] << size as u32; // shift for making room for extension
            self.buf[i].flip_bit(i); // set identity on extension
        }
    }

    fn degree(&self) -> usize {
        self.buf.iter().map(|poly| poly.degree()).max().unwrap_or(0)
    }

    fn gauss(&mut self) {
        let deg_matrix = self.degree();

        let mut pivot_i = 0;
        for deg_poly in (0..deg_matrix + 1).rev() {
            // find indice of first row with the this degree.
            let Some(selected_row_i) = self
                .buf
                .iter()
                .enumerate()
                .filter_map(|(x, pol)| {
                    if pol.degree() == deg_poly {
                        Some(x)
                    } else {
                        None
                    }
                })
                .next()
            else {
                continue;
            };

            // switch rows
            self.buf.swap(pivot_i, selected_row_i);

            let pivot = self.buf[pivot_i];
            if pivot.is_zero() {
                break;
            }
            for j in (pivot_i + 1)..deg_matrix {
                if self.buf[j].degree() == deg_poly && !self.buf[j].is_zero() {
                    self.buf[j] = self.buf[j] ^ pivot;
                }
            }

            pivot_i += 1;
        }
    }

    fn print_side_by_side(left: &Matrix, right: &Matrix) {
        let left_f = format!("{}", left);
        let right_f = format!("{}", right);

        for a in left_f.split("\n").zip(right_f.split("\n")) {
            println!("{} | {}", a.0, a.1);
        }
    }
}

impl Display for Matrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let size = self.degree();
        write!(
            f,
            "{}",
            self.buf
                .into_iter()
                .take(size)
                .map(|p| format!("{:032b}", p.buf[0]))
                .collect::<Vec<String>>()
                .join("\n")
        )
    }
}

fn decrypt(poly: Poly) -> Vec<Poly> {
    let sff = poly.sff();

    let factors: Vec<Poly> = sff
        .into_iter()
        .flat_map(|(num, pol)| berlekamp_factorize(pol).into_iter().map(move |f| (num, f)))
        .flat_map(|(num, pol)| std::iter::repeat_n(pol, num))
        .sorted()
        .collect();

    let product: Poly = factors.iter().cloned().product();
    if product != poly {
        println!("Cannot reconstruct original poly");
        println!("og: {poly}");
        println!("cp: {product}");
        println!("gcd: {}", Poly::gcd(poly, product));
        println!("--- factors");
        for f in &factors {
            println!("{f}");
        }
    }
    factors
}

fn berlekamp_factorize(poly: Poly) -> Vec<Poly> {
    assert!(!poly.is_square());
    let mut polynoms = vec![poly];
    let mut result = vec![];
    while !polynoms.is_empty() {
        let pol = polynoms.pop().unwrap();
        let factors = berlekamp_factorize_step(pol);
        if factors.len() > 1 {
            polynoms.extend(factors);
        } else {
            result.extend(factors);
        }
    }

    result.sort();

    // sanity check
    let rebuild: Poly = result.iter().cloned().product();
    if rebuild != poly {
        println!("Product is different from original");
        println!("original: {}", poly);
        println!("product: {}", rebuild);
        println!("--- factors:");
        for f in &result {
            println!("{}", f);
        }
    }
    result
}

fn berlekamp_factorize_step(poly: Poly) -> Vec<Poly> {
    let mut factors = vec![];
    let nvs: Vec<Poly> = M.with(|m| {
        let mut m = m.borrow_mut();
        m.zeroed();
        m.berlekamp(poly);
        m.gauss();
        m.buf
            .into_iter()
            .filter(|pol| pol.degree() <= poly.degree())
            .take_while(|pol| pol.degree() > 0)
            .collect()
    });

    for nv in &nvs {
        let mut nv = *nv;
        let factor = Poly::gcd(poly, nv);
        if factor.degree() > 0 {
            factors.push(factor);
        }

        nv.flip_bit(0);
        let factor = Poly::gcd(poly, nv);
        if factor.degree() > 0 {
            factors.push(factor);
        }
    }

    let mut result = vec![];
    factors.sort();

    let mut rem = poly;
    for f in factors {
        if rem % f == Poly::zero() {
            result.push(f);
            rem = rem / f;
        }

        if rem.is_one() {
            break;
        }
    }

    if !rem.is_one() {
        result.push(rem);
    }

    result.into_iter().unique().collect()
}

fn find_pairs(
    left: Poly,
    right: Poly,
    available_factors: &[Poly],
    max_degree: usize,
) -> Vec<(Poly, Poly)> {
    if left.degree() > max_degree {
        return vec![];
    }
    if right.degree() > max_degree {
        return vec![];
    }
    if available_factors.is_empty() {
        return vec![(left, right)];
    }

    let mut result = vec![];
    let next = available_factors[0];
    result.extend(find_pairs(
        left,
        right * next,
        &available_factors[1..],
        max_degree,
    ));
    result.extend(find_pairs(
        left * next,
        right,
        &available_factors[1..],
        max_degree,
    ));
    result
}

fn encrypt(size: usize, data: Vec<u32>) -> Vec<u32> {
    let n = size / 16;
    let a: Vec<_> = data.iter().take(n).collect();
    let mut b: Vec<_> = vec![0; n];

    for i in 0..size {
        for j in 0..size {
            let ij = i + j;
            let i_val = a[i / 32] >> (i % 32);
            let j_val = a[j / 32 + size / 32] >> (j % 32);
            b[ij / 32] ^= (i_val & j_val & 1) << (ij % 32);
        }
    }
    b
}

fn encrypt_poly(left: Poly, right: Poly) -> Poly {
    left * right
}

fn main() {
    let mut roots = vec![];
    for i in 2..100 {
        let pol = Poly::from_vec(vec![i]);
        let factors = decrypt(pol);
        if factors.len() == 1 {
            roots.push(pol);
        }
    }

    let mut to_visit = vec![(0, vec![])];
    let max_deg = 100;
    loop {
        let (n, polys) = to_visit.pop().unwrap();
        for i in (n)..roots.len() {
            let factor = roots[i];
            let product: Poly = polys.iter().cloned().product();
            let product: Poly = product * factor;
            println!("testing at {i} {product}");
            if product.degree() > max_deg {
                break;
            }

            let mut next = polys.clone();
            next.push(factor);
            to_visit.push((i + 1, next));

            let decomp = decrypt(product);

            let mut err = false;
            if decomp.len() != polys.len() + 1 {
                println!("decomp failed for: {product}");
                err = true;
            }
            if decomp.iter().cloned().product::<Poly>() != product {
                println!("decomp has changed the value");
                err = true;
            }
            if err {
                println!("--- initial");
                for f in &polys {
                    println!("{f}");
                }
                println!("{factor}");
                println!("--- computed");
                for f in decomp {
                    println!("{f}");
                }
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rsh() {
        let poly = Poly::from_vec(vec![0xff, 0x00, 0xAB, 0x3]);
        println!("original: {}", poly);
        println!("    >> 1: {}", poly >> 1);
        println!("    >> 9: {}", poly >> 9);
    }

    #[test]
    fn test_lsh() {
        let poly = Poly::from_vec(vec![0xff, 0x00, 0xAB, 0x3]);
        println!("original: {}", poly);
        println!("    << 1: {}", poly << 1);
        println!("    << 9: {}", poly << 9);
    }

    #[test]
    fn test_derivative() {
        let poly = Poly::from_vec(vec![0xff, 0x00, 0xAB, 0x3]);
        println!("original  : {}", poly);
        println!("derivative: {}", poly.derivative());
    }

    #[test]
    fn test_div() {
        let poly = Poly::from_vec(vec![0xff, 0x00, 0xAB, 0x4]);
        let poly_div = Poly::from_vec(vec![0xAB, 0x3]);

        let div = poly / poly_div;

        println!("original: {}", poly);
        println!(" divider: {}", poly_div);
        println!("  result: {}", div);
        println!(" rebuilt: {}", poly_div * div);
    }

    #[test]
    fn test_rem() {
        let poly = Poly::from_str("fffffffe");
        let poly_div = Poly::from_str("ffe");

        let rem = poly % poly_div;

        println!("original: {}", poly);
        println!(" divider: {}", poly_div);
        println!("  remain: {}", rem);
    }

    #[test]
    fn test_mul() {
        let poly_a = Poly::from_vec(vec![0xff, 0x00, 0xAB, 0x3]);
        let poly_b = Poly::from_str("3 ffffffffffffff10 5555555555557170");

        println!("A: {}", poly_a);
        println!("B: {}", poly_b);
        println!("P1: {}", poly_a * poly_b);
        println!("P2: {}", poly_b * poly_a);
    }

    #[test]
    fn test_gcd() {
        let pol_a = Poly::from_vec(vec![0xff, 0x00]);
        let pol_b = Poly::from_vec(vec![0xAB, 0x3]);
        let pol_c = Poly::from_vec(vec![0x8E, 0x37]);

        let gcd = Poly::gcd(pol_a * pol_b, pol_b * pol_c);

        println!("  gcd: {}", gcd);
        println!("pol_b: {}", pol_b);

        assert_eq!(gcd / pol_b, Poly::from_vec(vec!(1)));
    }

    #[test]
    fn test_factorize() {
        let poly_a = Poly::from_vec(vec![0xfe]);
        let poly_b = Poly::from_vec(vec![0b101]);
        let poly_c = Poly::from_vec(vec![0b101001]);

        println!("poly a: {}", poly_a);
        println!("poly b: {}", poly_b);
        println!("poly c: {}", poly_c);

        let poly = poly_a * poly_b * poly_c;

        println!("poly {}:", poly);
        println!("poly /a/b/c: {}", ((poly / poly_a) / poly_b) / poly_c);
        println!("poly /a: {}", poly / poly_a);
        for factor in berlekamp_factorize(poly) {
            println!("factor: {}", factor);
        }
    }

    macro_rules! test_decrypt {
        ($hex: literal) => {
            let pol = Poly::from_str($hex);
            println!("decrypting {pol}");
            let factors = decrypt(pol);

            println!("Summary:");
            println!("OG: {pol}");

            let rebuilt: Poly = factors.iter().cloned().product();
            println!("CP: {rebuilt}");

            println!("factors");
            for f in factors {
                println!("{f}");
            }
        };
    }

    #[test]
    fn test_59() {
        test_decrypt!("59");
    }

    #[test]
    fn test_5d() {
        test_decrypt!("5d");
    }

    #[test]
    fn test_beb() {
        test_decrypt!("beb");
    }

    #[test]
    fn test_ce5() {
        test_decrypt!("ce5");
    }

    #[test]
    fn test_1677() {
        test_decrypt!("1677");
    }

    #[test]
    fn test_1cbd() {
        test_decrypt!("1c1e");
    }

    #[test]
    fn test_codingame_32_1() {
        test_decrypt!("73af");
    }

    #[test]
    fn test_codingame_64() {
        test_decrypt!("65ee6bda 0b324559 661859eb f3268b49");
    }

    #[test]
    fn test_codingame_128() {
        test_decrypt!("128a91db473fcea8db4f3bb434a8dba2f1651abc87e92c447595c1a16d36111c6f4");
    }

    #[test]
    fn test_codinggame_256() {
        let value = "4af6fc33 39029380 465c5267 c72f6a8b 0906e6d0 ca60550f 14a5e47c 42ad10fb 4a3bb446 bb74360a 5ea02b9c 23c68553 3fade253 e270ba24 39e141ad 6c38c43d";
        let rev_val = value.split_whitespace().rev().join("");

        let pol = Poly::from_str(&rev_val);
        println!("{pol}");
        for f in decrypt(pol) {
            println!("{f}");
        }
    }
}
