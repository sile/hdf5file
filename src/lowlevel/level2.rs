use ndarray::ArrayD;

#[derive(Debug)]
pub enum DataObject {
    Float(ArrayD<f64>),
}
