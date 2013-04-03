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
#ifndef _WEKA_CPP_MATRIX_HPP_
#define _WEKA_CPP_MATRIX_HPP_

#include <iostream>
using namespace std; 

/**
 * Class for performing operations on a matrix of floating-point values.
 * <p/>
 * Deprecated: Uses internally the code of the sub-package 
 * <code>weka.core.matrix</code> - only for backwards compatibility.
 */
class Matrix : public RevisionHandler {

protected: 
  /**
   * The actual matrix */
  Matrix m_Matrix;

  /**
   * Constructs a matrix and initializes it with default values.
   *
   * @param nr the number of rows
   * @param nc the number of columns
   */
public:
    Matrix(int nr, int nc); 

  /**
   * Constructs a matrix using a given array.
   *
   * @param array the values of the matrix
   */
    Matrix(double** array, int nrow, int ncol);

  /**
   * Reads a matrix from a reader. The first line in the file should
   * contain the number of rows and columns. Subsequent lines
   * contain elements of the matrix.
   *
   * @param r the reader containing the matrix
   * @throws Exception if an error occurs
   */
    Matrix(Reader r);

    Matrix Matrix(const Matrix& other); 

  /**
   * Writes out a matrix.
   *
   * @param w the output Writer
   * @throws Exception if an error occurs
   */
    void write(Writer w); 

  /**
   * returns the internal matrix
   * @see #m_Matrix
   */
  inline weka.core.matrix.Matrix getMatrix() {
    return m_Matrix;
  }

  /**
   * Returns the value of a cell in the matrix.
   *
   * @param rowIndex the row's index
   * @param columnIndex the column's index
   * @return the value of the cell of the matrix
   */
  inline double getElement(int rowIndex, int columnIndex) {
    return m_Matrix.get(rowIndex, columnIndex);
  }

  /**
   * Add a value to an element.
   *
   * @param rowIndex the row's index.
   * @param columnIndex the column's index.
   * @param value the value to add.
   */
  inline void addElement(int rowIndex, int columnIndex, double value) {
    m_Matrix.set(
        rowIndex, columnIndex, m_Matrix.get(rowIndex, columnIndex) + value);
  }

  /**
   * Returns the number of rows in the matrix.
   *
   * @return the number of rows
   */
    inline int numRows() {
    return m_Matrix.getRowDimension();
  }

  /**
   * Returns the number of columns in the matrix.
   *
   * @return the number of columns
   */
    inline int numColumns() {
    return m_Matrix.getColumnDimension();
  }

  /**
   * Sets an element of the matrix to the given value.
   *
   * @param rowIndex the row's index
   * @param columnIndex the column's index
   * @param value the value
   */
    void setElement(int rowIndex, int columnIndex, double value); 

  /**
   * Sets a row of the matrix to the given row. Performs a deep copy.
   *
   * @param index the row's index
   * @param newRow an array of doubles
   */
    void setRow(int index, double* newRow, int numRowElem); 
  
  /**
   * Gets a row of the matrix and returns it as double array.
   *
   * @param index the row's index
   * @return an array of doubles
   */
    double* getRow(int index); 

  /**
   * Gets a column of the matrix and returns it as a double array.
   *
   * @param index the column's index
   * @return an array of doubles
   */
    double* getColumn(int index);

  /**
   * Sets a column of the matrix to the given column. Performs a deep copy.
   *
   * @param index the column's index
   * @param newColumn an array of doubles
   */
    void setColumn(int index, double newColumn, int cnt); 

  /** 
   * Converts a matrix to a string
   *
   * @return the converted string
   */
  inline string toString() {
    return m_Matrix.toString();
  } 
    
  /**
   * Returns the sum of this matrix with another.
   *
   * @return a matrix containing the sum.
   */
    Matrix add(Matrix other); 
  
  /**
   * Returns the transpose of a matrix.
   *
   * @return the transposition of this instance.
   */
    Matrix transpose(); 
  
  /**
   * Returns true if the matrix is symmetric.
   *
   * @return bool true if matrix is symmetric.
   */
  inline bool isSymmetric() {
    return m_Matrix.isSymmetric();
  }

  /**
   * Returns the multiplication of two matrices
   *
   * @param b the multiplication matrix
   * @return the product matrix
   */
    Matrix multiply(Matrix b); 

  /**
   * Performs a (ridged) linear regression.
   *
   * @param y the dependent variable vector
   * @param ridge the ridge parameter
   * @return the coefficients 
   * @throws IllegalArgumentException if not successful
   */
    double* regression(Matrix y, double ridge); 

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
    double* regression(Matrix y, double * w, int nw, double ridge); 

  /**
   * Returns the L part of the matrix.
   * This does only make sense after LU decomposition.
   *
   * @return matrix with the L part of the matrix; 
   * @see #LUDecomposition()
   */
    Matrix getL();

  /**
   * Returns the U part of the matrix.
   * This does only make sense after LU decomposition.
   *
   * @return matrix with the U part of a matrix; 
   * @see #LUDecomposition()
   */
    Matrix getU();
  
  /**
   * Performs a LUDecomposition on the matrix.
   * It changes the matrix into its LU decomposition.
   *
   * @return the indices of the row permutation
   */
    vector<int> LUDecomposition(); 
  
  /**
   * Solve A*X = B using backward substitution.
   * A is current object (this). Note that this matrix will be changed! 
   * B parameter bb.
   * X returned in parameter bb.
   *
   * @param bb first vector B in above equation then X in same equation.
   */
    void solve(double* bb, int len);

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
    void eigenvalueDecomposition(double** V, int nrowV, int ncolV, double* d); 

  /**
   * Returns sqrt(a^2 + b^2) without under/overflow.
   *   
   * @param a length of one side of rectangular triangle
   * @param b length of other side of rectangular triangle
   * @return lenght of third side
   */
protected: 
    static double hypot(double a, double b); 

public:
  /**
   * converts the Matrix into a single line Matlab string: matrix is enclosed 
   * by parentheses, rows are separated by semicolon and single cells by
   * blanks, e.g., [1 2; 3 4].
   * @return      the matrix in Matlab single line format
   */
    string toMatlab(); 

  /**
   * creates a matrix from the given Matlab string.
   * @param matlab  the matrix in matlab format
   * @return        the matrix represented by the given string
   * @see           #toMatlab()
   */
    static Matrix parseMatlab(string matlab);
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  inline string getRevision() {
    return RevisionUtils.extract("$Revision: 1.25 $");
  }

/**
 * Main method for testing this class.
 */
    static void main(string ops); 
};

#endif
