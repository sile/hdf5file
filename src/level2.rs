use ndarray::ArrayD;

#[derive(Debug)]
pub enum DataObject {
    Float(ArrayD<f64>),
}

// TODO: rename
#[derive(Debug)]
pub enum DataItem {
    Float(f64),
}
