use ndarray::ArrayD;

#[derive(Debug)]
pub enum DataObject {
    Float(ArrayD<f64>),
}

// TODO: rename
#[derive(Debug, Clone, PartialEq)]
pub enum DataItem {
    Float(f64),
}
