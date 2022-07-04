//! Module to argue that inner product of vectors <a, b> = c
#![allow(dead_code)]
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct ACell<F: FieldExt>(AssignedCell<F, F>);

/// Dimension of the vector.
const DIM: usize = 4;

/// This is a configuration file for the circuit layout.
/// The circuit will be a n by 2*DIM+3 matrix.
#[derive(Debug, Clone)]
struct InnerProductConfig {
    /// The witness columns for vectors a and b, and a single column for c
    pub advice: Vec<Column<Advice>>,
    /// Selector
    pub selector: Selector,
    /// The public input column.
    pub instance: Column<Instance>,
}

/// A InnerProduct chip is associated with a circuit-native prime field.
#[derive(Debug, Clone)]
struct InnerProductChip<F: FieldExt> {
    config: InnerProductConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> InnerProductChip<F> {
    pub fn construct(config: InnerProductConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: &[Column<Advice>],
        instance: Column<Instance>,
    ) -> InnerProductConfig {
        assert_eq!(advice.len(), 2 * DIM + 2);

        for ad in advice.iter() {
            meta.enable_equality(*ad)
        }
        meta.enable_equality(instance);

        let col_a_s = &advice[0..DIM];
        let col_b_s = &advice[DIM..DIM << 1];
        let carry = &advice[DIM << 1];
        let col_c = &advice[(DIM << 1) + 1];
        let selector = meta.selector();

        meta.create_gate("inner product", |meta| {
            //
            //   col_a_s   | col_b_s   |  carry  | col_c | selector
            //   a0...ad        b0...bd       carry       c              s
            //
            let s = meta.query_selector(selector);
            let a_i_s: Vec<Expression<F>> = (0..DIM)
                .map(|i| meta.query_advice(col_a_s[i], Rotation::cur()))
                .collect();
            let b_i_s: Vec<Expression<F>> = (0..DIM)
                .map(|i| meta.query_advice(col_b_s[i], Rotation::cur()))
                .collect();

            let c = meta.query_advice(*col_c, Rotation::cur());

            let mut res = meta.query_advice(*carry, Rotation::cur()).clone();
            for (a_i, b_i) in a_i_s.iter().zip(b_i_s.iter()) {
                res = res + a_i.clone() * b_i.clone();
            }

            vec![s * (res - c)]
        });

        InnerProductConfig {
            advice: advice.to_vec(),
            selector,
            instance,
        }
    }

    pub fn assign_first_row(&self, mut layouter: impl Layouter<F>) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let _a_cells: Vec<ACell<F>> = (0..DIM)
                    .map(|i| {
                        region
                            .assign_advice(
                                || "a",
                                self.config.advice[i],
                                0,
                                || Value::known(F::zero()),
                            )
                            .map(ACell)
                            .unwrap()
                    })
                    .collect();

                let _b_cells: Vec<ACell<F>> = (0..DIM)
                    .map(|i| {
                        region
                            .assign_advice(
                                || "b",
                                self.config.advice[4 + i],
                                0,
                                || Value::known(F::zero()),
                            )
                            .map(ACell)
                            .unwrap()
                    })
                    .collect();

                let _carry_cell = region
                    .assign_advice(|| "c", self.config.advice[8], 0, || Value::known(F::zero()))
                    .map(ACell)
                    .unwrap();

                let c_cell = region
                    .assign_advice(|| "c", self.config.advice[9], 0, || Value::known(F::zero()))
                    .map(ACell)
                    .unwrap();

                Ok(c_cell)
            },
        )
    }

    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        vec_a: &[Value<F>],
        vec_b: &[Value<F>],
        prev_c: &ACell<F>,
    ) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "Next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let _a_cells: Vec<ACell<F>> = vec_a
                    .iter()
                    .enumerate()
                    .map(|(i, &a)| {
                        region
                            .assign_advice(|| "a", self.config.advice[i], 0, || a)
                            .map(ACell)
                            .unwrap()
                    })
                    .collect();

                let _b_cells: Vec<ACell<F>> = vec_b
                    .iter()
                    .enumerate()
                    .map(|(i, &b)| {
                        region
                            .assign_advice(|| "b", self.config.advice[i + 4], 0, || b)
                            .map(ACell)
                            .unwrap()
                    })
                    .collect();

                let carry =
                    prev_c
                        .0
                        .copy_advice(|| "carry", &mut region, self.config.advice[8], 0)?;

                let mut c_val = carry.value().copied();
                for (&a, &b) in vec_a.iter().zip(vec_b.iter()) {
                    c_val = c_val + a * b;
                }

                let c_cell = region
                    .assign_advice(|| "c", self.config.advice[9], 0, || c_val)
                    .map(ACell)?;

                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &ACell<F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.0.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
/// Input to the inner argument <a, b> = c
struct MyCircuit<F> {
    pub a: Vec<Value<F>>,
    pub b: Vec<Value<F>>,
    pub c: Value<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = InnerProductConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let inputs: Vec<Column<Advice>> = (0..2 * DIM + 2).map(|_| meta.advice_column()).collect();

        let instance = meta.instance_column();
        InnerProductChip::configure(meta, inputs.as_ref(), instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = InnerProductChip::construct(config);

        let c_cell_0 = chip.assign_first_row(layouter.namespace(|| "inner product"))?;
        let c_cell_1 = chip.assign_row(
            layouter.namespace(|| "inner product"),
            &self.a[0..4],
            &self.b[0..4],
            &c_cell_0,
        )?;
        let c_cell_2 = chip.assign_row(
            layouter.namespace(|| "inner product"),
            &self.a[4..8],
            &self.b[4..8],
            &c_cell_1,
        )?;

        chip.expose_public(layouter.namespace(|| "out"), &c_cell_2, 0)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::MyCircuit;
    use halo2_proofs::{arithmetic::Field, circuit::Value, dev::MockProver, pasta::Fp};
    use rand::rngs::OsRng;

    fn make_test_vectors(n: usize) -> (Vec<Fp>, Vec<Fp>, Fp) {
        let mut rng = OsRng;
        let a: Vec<Fp> = (0..n).map(|_| Fp::random(&mut rng)).collect();

        let b: Vec<Fp> = (0..n).map(|_| Fp::random(&mut rng)).collect();

        let mut c = a[0] * b[0];
        for (&ai, &bi) in a.iter().zip(b.iter()).skip(1) {
            c = c + ai * bi;
        }

        (a, b, c)
    }

    #[test]
    fn test_inner_product() {
        let k = 4;

        let a1 = Fp::from(1);
        let a2 = Fp::from(2);
        let a3 = Fp::from(3);
        let a4 = Fp::from(4);

        let b1 = Fp::from(1);
        let b2 = Fp::from(1);
        let b3 = Fp::from(1);
        let b4 = Fp::from(1);

        let c = Fp::from(20);

        let circuit = MyCircuit {
            a: vec![
                Value::known(a1),
                Value::known(a2),
                Value::known(a3),
                Value::known(a4),
                Value::known(a1),
                Value::known(a2),
                Value::known(a3),
                Value::known(a4),
            ],
            b: vec![
                Value::known(b1),
                Value::known(b2),
                Value::known(b3),
                Value::known(b4),
                Value::known(b1),
                Value::known(b2),
                Value::known(b3),
                Value::known(b4),
            ],
            c: Value::known(c),
        };

        let public_input = vec![c];

        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        for _ in 0..10 {
            let (a, b, c) = make_test_vectors(8);

            let circuit = MyCircuit {
                a: a.iter().map(|&x| Value::known(x)).collect(),
                b: b.iter().map(|&x| Value::known(x)).collect(),
                c: Value::known(c),
            };

            let public_input = vec![c];

            let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
            prover.assert_satisfied();
        }

        // public_input[0] += Fp::one();
        // let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        // uncomment the following line and the assert will fail
        // _prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn test_inner_product_plot() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("inner_product.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("inner product", ("sans-serif", 60)).unwrap();

        let (a, b, c) = make_test_vectors(8);

        let circuit = MyCircuit {
            a: a.iter().map(|&x| Value::known(x)).collect(),
            b: b.iter().map(|&x| Value::known(x)).collect(),
            c: Value::known(c),
        };

        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
