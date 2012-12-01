#include "FastVector.hpp"

using namespace std; 

void FastVector::addElement(Object element) {

  Object[] newObjects;

  if (m_Size == m_Objects.length) {
    newObjects = new Object[m_CapacityMultiplier *
			    (m_Objects.length +
			     m_CapacityIncrement)];
    System.arraycopy(m_Objects, 0, newObjects, 0, m_Size);
    m_Objects = newObjects;
  }
  m_Objects[m_Size] = element;
  m_Size++;
}

Object FastVector::copy() {

  FastVector copy = new FastVector(m_Objects.length);

  copy.m_Size = m_Size;
  copy.m_CapacityIncrement = m_CapacityIncrement;
  copy.m_CapacityMultiplier = m_CapacityMultiplier;
  System.arraycopy(m_Objects, 0, copy.m_Objects, 0, m_Size);
  return copy;
}

Object FastVector::copyElements() {

  FastVector copy = new FastVector(m_Objects.length);

  copy.m_Size = m_Size;
  copy.m_CapacityIncrement = m_CapacityIncrement;
  copy.m_CapacityMultiplier = m_CapacityMultiplier;
  for (int i = 0; i < m_Size; i++) {
    copy.m_Objects[i] = ((Copyable)m_Objects[i]).copy();
  }
  return copy;
}

bool FastVector::contains(Object o) {
  if(o==NULL)
    return false;

  for(int i=0; i<m_Objects.length; i++) 
    if(o.equals(m_Objects[i]))
      return true;
      
  return false;
}


/**
 * Searches for the first occurence of the given argument, 
 * testing for equality using the equals method. 
 *
 * @param element the element to be found
 * @return the index of the first occurrence of the argument 
 * in this vector; returns -1 if the object is not found
 */
/ int FastVector::indexOf(/*@non_NULL@*/ Object element) {

  for (int i = 0; i < m_Size; i++) {
    if (element.equals(m_Objects[i])) {
      return i;
    }
  }
  return -1;
}

/**
 * Inserts an element at the given position.
 *
 * @param element the element to be inserted
 * @param index the element's index
 */
void FastVector::insertElementAt(Object element, int index) {

  Object[] newObjects;

  if (m_Size < m_Objects.length) {
    System.arraycopy(m_Objects, index, m_Objects, index + 1, 
		     m_Size - index);
    m_Objects[index] = element;
  } else {
    newObjects = new Object[m_CapacityMultiplier *
			    (m_Objects.length +
			     m_CapacityIncrement)];
    System.arraycopy(m_Objects, 0, newObjects, 0, index);
    newObjects[index] = element;
    System.arraycopy(m_Objects, index, newObjects, index + 1,
		     m_Size - index);
    m_Objects = newObjects;
  }
  m_Size++;
}

/**
 * Removes all components from this vector and sets its 
 * size to zero. 
 */
void FastVector::removeAllElements() {

  m_Objects = new Object[m_Objects.length];
  m_Size = 0;
}

/**
 * Swaps two elements in the vector.
 *
 * @param first index of the first element
 * @param second index of the second element
 */
//@ requires 0 <= first && first < size();
//@ requires 0 <= second && second < size();
void FastVector::swap(int first, int second) {

  Object help = m_Objects[first];

  m_Objects[first] = m_Objects[second];
  m_Objects[second] = help;
}
