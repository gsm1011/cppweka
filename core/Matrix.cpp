/*
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License as published by
 *    the Free Software Foundation; either version 2 of the License, or
 *    (at your option) any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

/*
 *    Matrix.cpp
 *    Copyright (C) 1999 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import java.io.Reader;
// import java.io.Serializable;
// import java.io.Writer;

/**
 * Class for performing operations on a matrix of floating-point values.
 * <p/>
 * Deprecated: Uses internally the code of the sub-package 
 * <code>weka.core.matrix</code> - only for backwards compatibility.
 *
 * @author Gabi Schmidberger (gabi@cs.waikato.ac.nz)
 * @author Yong Wang (yongwang@cs.waikato.ac.nz)
 * @author Eibe Frank (eibe@cs.waikato.ac.nz)
 * @author Len Trigg (eibe@cs.waikato.ac.nz)
 * @author Fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.25 $
 * @deprecated Use <code>weka.core.matrix.Matrix</code> instead - only for
 * backwards compatibility. 
 */
class Matrix : public Cloneable, 
	       
	       public RevisionHandler {

  /** for serialization */
  // // // // private static long serialVersionUID = -3604757095849145838L;
protected: 
  /**
   * The actual matrix */
  weka.core.matrix.Matrix m_Matrix = NULL;

  /**
   * Constructs a matrix and initializes it with default values.
   *
   * @param nr the number of rows
   * @param nc the number of columns
   */
public:
  Matrix(int nr, int nc) {
    m_Matrix = new weka.core.matrix.Matrix(nr, nc);
  }

  /**
   * Constructs a matrix using a given array.
   *
   * @param array the values of the matrix
   */
  Matrix(double[][] array) throws Exception {
    m_Matrix = new weka.core.matrix.Matrix(array);
  }

  /**
   * Reads a matrix from a reader. The first line in the file should
   * contain the number of rows and columns. Subsequent lines
   * contain elements of the matrix.
   *
   * @param r the reader containing the matrix
   * @throws Exception if an error occurs
   */
  Matrix(Reader r) throws Exception {
    m_Matrix = new weka.core.matrix.Matrix(r);
  }

  /**
   * Creates and returns a clone of this object.
   *
   * @return a clone of this instance.
   * @throws Exception if an error occurs
   */
  Object clone() {
    try {
      return new Matrix(m_Matrix.getArrayCopy());
    }
    catch (Exception e) {
      e.printStackTrace();
      return NULL;
    }
  }

  /**
   * Writes out a matrix.
   *
   * @param w the output Writer
   * @throws Exception if an error occurs
   */
  void write(Writer w) throws Exception {
    m_Matrix.write(w);
  }

  /**
   * returns the internal matrix
   * @see #m_Matrix
   */
  weka.core.matrix.Matrix getMatrix() {
    return m_Matrix;
  }

  /**
   * Returns the value of a cell in the matrix.
   *
   * @param rowIndex the row's index
   * @param columnIndex the column's index
   * @return the value of the cell of the matrix
   */
  double getElement(int rowIndex, int columnIndex) {
    return m_Matrix.get(rowIndex, columnIndex);
  }

  /**
   * Add a value to an element.
   *
   * @param rowIndex the row's index.
   * @param columnIndex the column's index.
   * @param value the value to add.
   */
  void addElement(int rowIndex, int columnIndex, double value) {
    m_Matrix.set(
        rowIndex, columnIndex, m_Matrix.get(rowIndex, columnIndex) + value);
  }

  /**
   * Returns the number of rows in the matrix.
   *
   * @return the number of rows
   */
  int numRows() {
    return m_Matrix.getRowDimension();
  }

  /**
   * Returns the number of columns in the matrix.
   *
   * @return the number of columns
   */
  int numColumns() {
    return m_Matrix.getColumnDimension();
  }

  /**
   * Sets an element of the matrix to the given value.
   *
   * @param rowIndex the row's index
   * @param columnIndex the column's index
   * @param value the value
   */
  void setElement(int rowIndex, int columnIndex, double value) {
    m_Matrix.set(rowIndex, columnIndex, value);
  }

  /**
   * Sets a row of the matrix to the given row. Performs a deep copy.
   *
   * @param index the row's index
   * @param newRow an array of doubles
   */
  void setRow(int index, double[] newRow) {
    for (int i = 0; i < newRow.length; i++)
      m_Matrix.set(index, i, newRow[i]);
  }
  
  /**
   * Gets a row of the matrix and returns it as double array.
   *
   * @param index the row's index
   * @return an array of doubles
   */
  double[] getRow(int index) {
    double[] newRow = new double[this->numColumns()];
    for (int i = 0; i < newRow.length; i++)
      newRow[i] = getElement(index, i);

    return newRow;
  }

  /**
   * Gets a column of the matrix and returns it as a double array.
   *
   * @param index the column's index
   * @return an array of doubles
   */
  double[] getColumn(int index) {
    double[] newColumn = new double[this->numRows()];
    for (int i = 0; i < newColumn.length; i++)
      newColumn[i] = getElement(i, index);

    return newColumn;
  }

  /**
   * Sets a column of the matrix to the given column. Performs a deep copy.
   *
   * @param index the column's index
   * @param newColumn an array of doubles
   */
  void setColumn(int index, double[] newColumn) {
    for (int i = 0; i < numRows(); i++)
      m_Matrix.set(i, index, newColumn[i]);
  }

  /** 
   * Converts a matrix to a string
   *
   * @return the converted string
   */
  string toString() {
    return m_Matrix.toString();
  } 
    
  /**
   * Returns the sum of this matrix with another.
   *
   * @return a matrix containing the sum.
   */
  Matrix add(Matrix other) {
    try {
      return new Matrix(m_Matrix.plus(other.getMatrix()).getArrayCopy());
    }
    catch (Exception e) {
      e.printStackTrace();
      return NULL;
    }
  }
  
  /**
   * Returns the transpose of a matrix.
   *
   * @return the transposition of this instance.
   */
  Matrix transpose() {
    try {
      return new Matrix(m_Matrix.transpose().getArrayCopy());
    }
    catch (Exception e) {
      e.printStackTrace();
      return NULL;
    }
  }
  
  /**
   * Returns true if the matrix is symmetric.
   *
   * @return bool true if matrix is symmetric.
   */
  bool isSymmetric() {
    return m_Matrix.isSymmetric();
  }

  /**
   * Returns the multiplication of two matrices
   *
   * @param b the multiplication matrix
   * @return the product matrix
   */
  Matrix multiply(Matrix b) {
    try {
      return new Matrix(getMatrix().times(b.getMatrix()).getArrayCopy());
    }
    catch (Exception e) {
      e.printStackTrace();
      return NULL;
    }
  }

  /**
   * Performs a (ridged) linear regression.
   *
   * @param y the dependent variable vector
   * @param ridge the ridge parameter
   * @return the coefficients 
   * @throws IllegalArgumentException if not successful
   */
  double[] regression(Matrix y, double ridge) {
    return getMatrix().regression(y.getMatrix(), ridge).getCoefficients();
  }

  /**
   * Performs a weighted (ridged) linear regression. 
   *
   * @param y the dependent variable vector
   * @param w the array of data point weights
   * @param ridge the ridge parameter
   * @return the coefficients 
   * @throws IllegalArgumentException if the wrong number of weights were
   * provided.
   */
  double[] regression(Matrix y, double [] w, double ridge) {
    return getMatrix().regression(y.getMatrix(), w, ridge).getCoefficients();
  }

  /**
   * Returns the L part of the matrix.
   * This does only make sense after LU decomposition.
   *
   * @return matrix with the L part of the matrix; 
   * @see #LUDecomposition()
   */
  Matrix getL() throws Exception {
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

  /**
   * Returns the U part of the matrix.
   * This does only make sense after LU decomposition.
   *
   * @return matrix with the U part of a matrix; 
   * @see #LUDecomposition()
   */
  Matrix getU() throws Exception {
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
  
  /**
   * Performs a LUDecomposition on the matrix.
   * It changes the matrix into its LU decomposition.
   *
   * @return the indices of the row permutation
   */
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
  
  /**
   * Solve A*X = B using backward substitution.
   * A is current object (this). Note that this matrix will be changed! 
   * B parameter bb.
   * X returned in parameter bb.
   *
   * @param bb first vector B in above equation then X in same equation.
   */
  void solve(double[] bb) throws Exception {
    // solve
    weka.core.matrix.Matrix x = m_Matrix.solve(
                                    new weka.core.matrix.Matrix(bb, bb.length));
    
    // move X into bb
    int nr = x.getRowDimension();
    for (int i = 0; i < nr; i++)
      bb[i] = x.get(i, 0);
  }

  /**
   * Performs Eigenvalue Decomposition using Householder QR Factorization
   *
   * Matrix must be symmetrical.
   * Eigenvectors are return in parameter V, as columns of the 2D array.
   * (Real parts of) Eigenvalues are returned in parameter d.
   *
   * @param V double array in which the eigenvectors are returned 
   * @param d array in which the eigenvalues are returned
   * @throws Exception if matrix is not symmetric
   */
  void eigenvalueDecomposition(double[][] V, double[] d) 
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

  /**
   * Returns sqrt(a^2 + b^2) without under/overflow.
   *   
   * @param a length of one side of rectangular triangle
   * @param b length of other side of rectangular triangle
   * @return lenght of third side
   */
protected: 
  static double hypot(double a, double b) {
    return weka.core.matrix.Maths.hypot(a, b);
  }

public:
  /**
   * converts the Matrix into a single line Matlab string: matrix is enclosed 
   * by parentheses, rows are separated by semicolon and single cells by
   * blanks, e.g., [1 2; 3 4].
   * @return      the matrix in Matlab single line format
   */
  string toMatlab() {
    return getMatrix().toMatlab();
  }

  /**
   * creates a matrix from the given Matlab string.
   * @param matlab  the matrix in matlab format
   * @return        the matrix represented by the given string
   * @see           #toMatlab()
   */
  static Matrix parseMatlab(string matlab) throws Exception {
    return new Matrix(weka.core.matrix.Matrix.parseMatlab(matlab).getArray());
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.25 $");
  }
};

/**
 * Main method for testing this class.
 */
static void main(String[] ops) {

  double[] first = {2.3, 1.2, 5};
  double[] second = {5.2, 1.4, 9};
  double[] response = {4, 7, 8};
  double[] weights = {1, 2, 3};

  try {
    // test eigenvaluedecomposition
    double[][] m = {{1, 2, 3}, {2, 5, 6},{3, 6, 9}};
    Matrix M = new Matrix(m);
    int n = M.numRows();
    double[][] V = new double[n][n];
    double[] d = new double[n];
    double[] e = new double[n];
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

