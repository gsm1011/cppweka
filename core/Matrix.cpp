#include "Matrix.hpp"

Matrix::Matrix(int nr, int nc) {
    m_Matrix = new weka.core.matrix.Matrix(nr, nc);
}

Matrix::Matrix(double** array, int nrow, int ncol) {
    m_Matrix = new weka.core.matrix.Matrix(array);
}

Matrix::Matrix(Reader r) {
    m_Matrix = new weka.core.matrix.Matrix(r);
}

Matrix Matrix::Matrix() {

}

void Matrix::write(Writer w) throws Exception {
    m_Matrix.write(w);
}

double Matrix::getElement(int rowIndex, int columnIndex) {
    return m_Matrix.get(rowIndex, columnIndex);
}

void Matrix::addElement(int rowIndex, int columnIndex, double value) {
    m_Matrix.set(
		 rowIndex, columnIndex, m_Matrix.get(rowIndex, columnIndex) + value);
}

void Matrix::setElement(int rowIndex, int columnIndex, double value) {
    m_Matrix.set(rowIndex, columnIndex, value);
}

void Matrix::setRow(int index, double[] newRow) {
    for (int i = 0; i < newRow.length; i++)
	m_Matrix.set(index, i, newRow[i]);
}
  
double[] Matrix::getRow(int index) {
    double[] newRow = new double[this->numColumns()];
    for (int i = 0; i < newRow.length; i++)
	newRow[i] = getElement(index, i);

    return newRow;
}

double[] Matrix::getColumn(int index) {
    double[] newColumn = new double[this->numRows()];
    for (int i = 0; i < newColumn.length; i++)
	newColumn[i] = getElement(i, index);

    return newColumn;
}

void Matrix::setColumn(int index, double[] newColumn) {
    for (int i = 0; i < numRows(); i++)
	m_Matrix.set(i, index, newColumn[i]);
}

Matrix Matrix::add(Matrix other) {
    try {
	return new Matrix(m_Matrix.plus(other.getMatrix()).getArrayCopy());
    }
    catch (Exception e) {
	e.printStackTrace();
	return NULL;
    }
}
  
Matrix Matrix::transpose() {
    try {
	return new Matrix(m_Matrix.transpose().getArrayCopy());
    }
    catch (Exception e) {
	e.printStackTrace();
	return NULL;
    }
}
  
Matrix Matrix::multiply(Matrix b) {
    try {
	return new Matrix(getMatrix().times(b.getMatrix()).getArrayCopy());
    }
    catch (Exception e) {
	e.printStackTrace();
	return NULL;
    }
}

double[] regression(Matrix y, double ridge) {
    return getMatrix().regression(y.getMatrix(), ridge).getCoefficients();
}

double[] regression(Matrix y, double [] w, double ridge) {
    return getMatrix().regression(y.getMatrix(), w, ridge).getCoefficients();
}

Matrix Matrix::getL() throws Exception {
    int nr = numRows();    // num of rows
    int nc = numColumns(); // num of columns
    double[][] ld = new double[nr][nc];

    for (int i = 0; i < nr; i++) {
	for (int j = 0; (j < i) && (j < nc); j++) {
	    ld[i][j] = getElement(i, j);
	}
	if (i < nc) ld[i][i] = 1;
    }
    Matrix l = new Matrix(ld);
    return l;
}

Matrix Matrix::getU() throws Exception {
    int nr = numRows();    // num of rows
    int nc = numColumns(); // num of columns
    double[][] ud = new double[nr][nc];

    for (int i = 0; i < nr; i++) {
	for (int j = i; j < nc ; j++) {
	    ud[i][j] = getElement(i, j);
	}
    }
    Matrix u = new Matrix(ud);
    return u;
}
  
int[] LUDecomposition() throws Exception {
    // decompose
    weka.core.matrix.LUDecomposition lu = m_Matrix.lu();

    // singular? old class throws Exception!
    if (!lu.isNonsingular())
    	throw Exception("Matrix is singular");

    weka.core.matrix.Matrix u = lu.getU();
    weka.core.matrix.Matrix l = lu.getL();

    // modify internal matrix
    int nr = numRows();
    int nc = numColumns();
    for (int i = 0; i < nr; i++) {
	for (int j = 0; j < nc; j++) {
	    if (j < i)
		setElement(i, j, l.get(i, j));
	    else
		setElement(i, j, u.get(i, j));
	}
    }

    u = NULL;
    l = NULL;
    
    return lu.getPivot();
}
  
void Matrix::solve(double[] bb) throws Exception {
    // solve
    weka.core.matrix.Matrix x = m_Matrix.solve(
					       new weka.core.matrix.Matrix(bb, bb.length));
    
    // move X into bb
    int nr = x.getRowDimension();
    for (int i = 0; i < nr; i++)
	bb[i] = x.get(i, 0);
}

void Matrix::eigenvalueDecomposition(double[][] V, double[] d) 
    throws Exception {

    // old class only worked with symmetric matrices!
    if (!this->isSymmetric())
	throw Exception("EigenvalueDecomposition: Matrix must be symmetric.");
    
    // perform eigenvalue decomposition
    weka.core.matrix.EigenvalueDecomposition eig = m_Matrix.eig();
    weka.core.matrix.Matrix v = eig.getV();
    double[] d2 = eig.getRealEigenvalues();
    
    // transfer data
    int nr = numRows();
    int nc = numColumns();
    for (int i = 0; i < nr; i++)
	for (int j = 0; j < nc; j++)
	    V[i][j] = v.get(i, j);

    for (int i = 0; i < d2.length; i++)
	d[i] = d2[i];
} 

protected: 
static double Matrix::hypot(double a, double b) {
    return weka.core.matrix.Maths.hypot(a, b);
}

public:
string Matrix::toMatlab() {
    return getMatrix().toMatlab();
}

static Matrix Matrix::parseMatlab(string matlab) throws Exception {
    return new Matrix(weka.core.matrix.Matrix.parseMatlab(matlab).getArray());
}
  
static void Matrix::main(String[] ops) {

    double first[] = {2.3, 1.2, 5};
    double second[] = {5.2, 1.4, 9};
    double response[] = {4, 7, 8};
    double weights[] = {1, 2, 3};

    try {
	// test eigenvaluedecomposition
	double m[][] = {{1, 2, 3}, {2, 5, 6},{3, 6, 9}};
	Matrix M = new Matrix(m);
	int n = M.numRows();
	double V[][] = new double[n][n];
	double d [] = new double[n];
	double e [] = new double[n];
	M.eigenvalueDecomposition(V, d);
	Matrix v = new Matrix(V);
	// M.testEigen(v, d, );
	// end of test-eigenvaluedecomposition
      
	Matrix a = new Matrix(2, 3);
	Matrix b = new Matrix(3, 2);
	System.out.println("Number of columns for a: " + a.numColumns());
	System.out.println("Number of rows for a: " + a.numRows());
	a.setRow(0, first);
	a.setRow(1, second);
	b.setColumn(0, first);
	b.setColumn(1, second);
	System.out.println("a:\n " + a);
	System.out.println("b:\n " + b);
	System.out.println("a (0, 0): " + a.getElement(0, 0));
	System.out.println("a transposed:\n " + a.transpose());
	System.out.println("a * b:\n " + a.multiply(b));
	Matrix r = new Matrix(3, 1);
	r.setColumn(0, response);
	System.out.println("r:\n " + r);
	System.out.println("Coefficients of regression of b on r: ");
	double[] coefficients = b.regression(r, 1.0e-8);
	for (int i = 0; i < coefficients.length; i++) {
	    System.out.print(coefficients[i] + " ");
	}
	System.out.println();
	System.out.println("Weights: ");
	for (int i = 0; i < weights.length; i++) {
	    System.out.print(weights[i] + " ");
	}
	System.out.println();
	System.out.println("Coefficients of weighted regression of b on r: ");
	coefficients = b.regression(r, weights, 1.0e-8);
	for (int i = 0; i < coefficients.length; i++) {
	    System.out.print(coefficients[i] + " ");
	}
	System.out.println();
	a.setElement(0, 0, 6);
	System.out.println("a with (0, 0) set to 6:\n " + a);
	a.write(new java.io.FileWriter("main.matrix"));
	System.out.println("wrote matrix to \"main.matrix\"\n" + a);
	a = new Matrix(new java.io.FileReader("main.matrix"));
	System.out.println("read matrix from \"main.matrix\"\n" + a);
    } catch (Exception e) {
	e.printStackTrace();
    }
}
