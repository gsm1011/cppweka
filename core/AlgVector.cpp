#include "AlgVector.hpp"

using namespace std;

AlgVector::AlgVector(vector<double> array) {
  int len = array.size(); 
  m_Elements = (double*)malloc(sizeof(double) * len);
  for (int i = 0; i < len; i++) {
    m_Elements[i] = array[i];
  }
}

AlgVector::AlgVector(Instances format) {

  int len = format.numAttributes();
  for (int i = 0; i < len; i++) {
    if (!format.attribute(i).isNumeric()) len--;
  }
  if (len > 0) {
    m_Elements = (double *)malloc(sizeof(double) * len);
    initialize(true);
  }
}

AlgVector::AlgVector(const Instance& instance) {

  int len = instance.numAttributes();
  for (int i = 0; i < instance.numAttributes(); i++) {
    if (!instance.attribute(i).isNumeric())
      len--;
  }
  if (len > 0) {
    m_Elements = (double *)malloc(sizeof(double) * sizeof); 
    int n = 0;
    for (int i = 0; i < instance.numAttributes(); i++) {
      if (!instance.attribute(i).isNumeric())
	continue;
      m_Elements[n] = instance.value(i);
      n++;
    }
  } else {
    throw new IllegalArgumentException("No numeric attributes in data!");
  }
}

void AlgVector::initialize(bool isRand) {
  if(isRand) {
    srand(time(NULL));
    for (int i = 0; i < m_numElements; i++) {
      m_Elements[i] = rand();
    }
  } else {

    for (int i = 0; i < m_numElements; i++) {
        m_Elements[i] = 0.0;
    }
  }
}

double* AlgVector::getElements() {

  double* elements = (double*)malloc(sizeof(double) * m_numElements); 
    for (int i = 0; i < m_numElements; i++) {
        elements[i] = m_Elements[i];
    }
    return elements;
}

Instance AlgVector::getAsInstance(Instances model) {

    Instance newInst;

    if (m_Elements != NULL) {
        newInst = new Instance(model.numAttributes());
        newInst.setDataset(model);

        for (int i = 0, j = 0; i < model.numAttributes(); i++) {
            if (model.attribute(i).isNumeric()) {
                if (j >= m_Elements.length)
                    throw Exception("Datatypes are not compatible.");
                newInst.setValue(i, m_Elements[j++]);
            }
            if (model.attribute(i).isNominal()) {
                int newVal = (int)
		  (rand() * (double) (model.attribute(i).numValues()));
                if (newVal == (int) model.attribute(i).numValues())
                    newVal -= 1;
                newInst.setValue(i, newVal);
            }
        }
    }
    return newInst;
}

const AlgVector::AlgVector add(AlgVector other) {

    AlgVector b = NULL;

    if (m_Elements != NULL) {
        int n = m_Elements.length;
        try {
            b = (AlgVector)clone();
        } catch (CloneNotSupportedException ex) {
            b = new AlgVector(n);
        }

        for(int i = 0; i < n; i++) {
            b.m_Elements[i] = m_Elements[i] + other.m_Elements[i];
        }
    }

    return b;
}

const AlgVector::AlgVector substract(AlgVector other) {

  int n = m_numElements; 
    AlgVector b;
    try {
        b = (AlgVector)clone();
    } catch (CloneNotSupportedException ex) {
        b = new AlgVector(n);
    }

    for(int i = 0; i < n; i++) {
        b.m_Elements[i] = m_Elements[i] - other.m_Elements[i];
    }

    return b;
}

const double AlgVector::dotMultiply(AlgVector b) {

    double sum = 0.0;

    if (m_Elements != NULL) {
        int n = m_Elements.length;

        for(int i = 0; i < n; i++) {
            sum += m_Elements[i] * b.m_Elements[i];
        }
    }

    return sum;
}

const void AlgVector::scalarMultiply(double s) {

    if (m_Elements != NULL) {
        int n = m_Elements.length;

        for(int i = 0; i < n; i++) {
            m_Elements[i] = s * m_Elements[i];
        }
    }
}


void AlgVector::changeLength(double len) {

    double factor = this->norm();
    factor = len / factor;
    scalarMultiply(factor);
}

double AlgVector::norm() {

    if (m_Elements != NULL) {
        int n = m_Elements.length;
        double sum = 0.0;

        for(int i = 0; i < n; i++) {
            sum += m_Elements[i] * m_Elements[i];
        }
        return pow(sum, 0.5);
    } else return 0.0;
}

const void AlgVector::normVector() {

    double len = this->norm();
    this->scalarMultiply(1 / len);
}

string AlgVector::toString() {

    StringBuffer text = new StringBuffer();
    for (int i = 0; i < m_Elements.length; i++) {
        if (i > 0) text.append(",");
        text.append(Utils.doubleToString(m_Elements[i],6));
    }

    text.append("\n");
    return text.toString();
}

/**
 * Main method for testing this class, can take an ARFF file as first argument.
 *
 * @param args 	commandline options
 * @throws Exception	if something goes wrong in testing
 */
/*void main(int argc, char* argv[]) throws Exception {

    double[] first = {2.3, 1.2, 5.0};

    try {
        AlgVector test = new AlgVector(first);
        cout << "test:\n " << test << endl;

    } catch (Exception e) {
        e.printStackTrace();
    }
}
*/
