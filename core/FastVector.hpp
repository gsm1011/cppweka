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
 *    FastVector.cpp
 *    Copyright (C) 1999 University of Waikato, Hamilton, New Zealand
 *
 */
#ifndef _WEKA_FASTVECTOR_H_
#define  _WEKA_FASTVECTOR_H_
// package weka.core;

// import java.io.Serializable;
// import java.util.Enumeration;
#include <iostream>
#include <string>
#include <vector>
#include "Random.hpp"
#include "Copyable.hpp"
#include "Serializable.hpp"
#include "RevisionHandler.hpp"

using namespace std;
/**
 * Implements a fast vector class without synchronized
 * methods. Replaces java.util.Vector. (Synchronized methods tend to
 * be slow.)
 *
 * @author Eibe Frank (eibe@cs.waikato.ac.nz)
 * @version $Revision: 1.16 $
 */
class FastVector : public Copyable, public Serializable, public RevisionHandler {

public:
    void readObject() {
        return;
    }

    void writeObject() {
        return;
    }

    string getRevision() {
        return "1.0";
    }
    /** for serialization */
    // // // // private static long serialVersionUID = -2173635135622930169L;

    /**
     * Class for enumerating the vector's elements.
     */
public:
    class FastVectorEnumeration : public Enumeration,
        public RevisionHandler {
    private:
        /** The counter. */
        int m_Counter;
        // These JML commands say how m_Counter implements Enumeration
        //@ in moreElements;
        //@ private represents moreElements = m_Counter < m_Vector.size();
        //@ private invariant 0 <= m_Counter && m_Counter <= m_Vector.size();

        /** The vector. */
        /*@non_NULL@*/
        FastVector m_Vector;

        /** Special element. Skipped during enumeration. */
        int m_SpecialElement;
        //@ private invariant -1 <= m_SpecialElement;
        //@ private invariant m_SpecialElement < m_Vector.size();
        //@ private invariant m_SpecialElement>=0 ==> m_Counter!=m_SpecialElement;

        /**
         * Constructs an enumeration.
         *
         * @param vector the vector which is to be enumerated
         */
    public:
        FastVectorEnumeration(/*@non_NULL@*/FastVector vector) {

            m_Counter = 0;
            m_Vector = vector;
            m_SpecialElement = -1;
        }

        /**
         * Constructs an enumeration with a special element.
         * The special element is skipped during the enumeration.
         *
         * @param vector the vector which is to be enumerated
         * @param special the index of the special element
         */
        //@ requires 0 <= special && special < vector.size();
        FastVectorEnumeration(/*@non_NULL@*/FastVector vector, int special) {

            m_Vector = vector;
            m_SpecialElement = special;
            if (special == 0) {
                m_Counter = 1;
            } else {
                m_Counter = 0;
            }
        }


        /**
         * Tests if there are any more elements to enumerate.
         *
         * @return true if there are some elements left
         */
        /*@pure@*/ bool hasMoreElements() {

            if (m_Counter < m_Vector.size()) {
                return true;
            }
            return false;
        }

        /**
         * Returns the next element.
         *
         * @return the next element to be enumerated
         */
        //@ also requires hasMoreElements();
        Object nextElement() {

            Object result = m_Vector.elementAt(m_Counter);

            m_Counter++;
            if (m_Counter == m_SpecialElement) {
                m_Counter++;
            }
            return result;
        }

        /**
         * Returns the revision string.
         *
         * @return		the revision
         */
        string getRevision() {
            return RevisionUtils.extract("$Revision: 1.16 $");
        }
    };

private:
    /** The array of objects. */
    /*@spec_public@*/
    Object m_Objects[];
    //@ invariant m_Objects != NULL;
    //@ invariant m_Objects.length >= 0;

    /** The current size; */
    /*@spec_public@*/
    int m_Size;
    //@ invariant 0 <= m_Size;
    //@ invariant m_Size <= m_Objects.length;

    /** The capacity increment */
    /*@spec_public@*/
    int m_CapacityIncrement;
    //@ invariant 1 <= m_CapacityIncrement;

    /** The capacity multiplier. */
    /*@spec_public@*/
    int m_CapacityMultiplier;
    //@ invariant 1 <= m_CapacityMultiplier;

    // Make sure the size will increase...
    //@ invariant 3 <= m_CapacityMultiplier + m_CapacityIncrement;

public:
    void init() {
        m_Size = 0;
        m_CapacityIncrement = 1;
        m_CapacityMultiplier = 2;
    }
    /**
     * Constructs an empty vector with initial
     * capacity zero.
     */
    FastVector() {

        init();
        m_Objects = new Object[0];
    }

    /**
     * Constructs a vector with the given capacity.
     *
     * @param capacity the vector's initial capacity
     */
    //@ requires capacity >= 0;
    FastVector(int capacity) {

        init();
        m_Objects = new Object[capacity];
    }

    /**
     * Adds an element to this vector. Increases its
     * capacity if its not large enough.
     *
     * @param element the element to add
     */
    void addElement(Object element);

    /**
     * Returns the capacity of the vector.
     *
     * @return the capacity of the vector
     */
    //@ ensures \result == m_Objects.length;
    /*@pure@*/
    int capacity() {

        return m_Objects.length;
    }

    /**
     * Produces a shallow copy of this vector.
     *
     * @return the new vector
     */
    // Object copy();

    /**
     * Clones the vector and shallow copies all its elements.
     * The elements have to implement the Copyable interface.
     *
     * @return the new vector
     */
    Object copyElements();

    /**
     * Returns the element at the given position.
     *
     * @param index the element's index
     * @return the element with the given index
     */
    //@ requires 0 <= index;
    //@ requires index < m_Objects.length;
    /*@pure@*/
    Object elementAt(int index) {

        return m_Objects[index];
    }

    /**
     * Returns an enumeration of this vector.
     *
     * @return an enumeration of this vector
     */
    // /*@pure@*/ Enumeration elements() {

    //   return new FastVectorEnumeration(this);
    // }

    /**
     * Returns an enumeration of this vector, skipping the
     * element with the given index.
     *
     * @param index the element to skip
     * @return an enumeration of this vector
     */
    //@ requires 0 <= index && index < size();
    //  /*@pure@*/ Enumeration elements(int index) {
    //
    //  return new FastVectorEnumeration(this, index);
    // }

    /**
     * added by akibriya
     */
    /*@pure@*/ bool contains(Object o);

    /**
     * Returns the first element of the vector.
     *
     * @return the first element of the vector
     */
    //@ requires m_Size > 0;
    /*@pure@*/
    Object firstElement() {

        return m_Objects[0];
    }

    /**
     * Searches for the first occurence of the given argument,
     * testing for equality using the equals method.
     *
     * @param element the element to be found
     * @return the index of the first occurrence of the argument
     * in this vector; returns -1 if the object is not found
     */
    /*@pure@*/ int indexOf(/*@non_NULL@*/ Object element);

    /**
     * Inserts an element at the given position.
     *
     * @param element the element to be inserted
     * @param index the element's index
     */
    void insertElementAt(Object element, int index);

    /**
     * Returns the last element of the vector.
     *
     * @return the last element of the vector
     */
    //@ requires m_Size > 0;
    /*@pure@*/
    Object lastElement() {

        return m_Objects[m_Size - 1];
    }

    /**
     * Deletes an element from this vector.
     *
     * @param index the index of the element to be deleted
     */
    //@ requires 0 <= index && index < m_Size;
    void removeElementAt(int index) {

        System.arraycopy(m_Objects, index + 1, m_Objects, index,
                         m_Size - index - 1);

        // clear the last reference
        m_Objects[m_Size - 1] = NULL;

        m_Size--;
    }

    /**
     * Removes all components from this vector and sets its
     * size to zero.
     */
    void removeAllElements();

    /**
     * Appends all elements of the supplied vector to this vector.
     *
     * @param toAppend the FastVector containing elements to append.
     */
    void appendElements(FastVector toAppend) {

        setCapacity(size() + toAppend.size());
        System.arraycopy(toAppend.m_Objects, 0, m_Objects, size(), toAppend.size());
        m_Size = m_Objects.length();
    }

    /**
     * Returns all the elements of this vector as an array
     *
     * @return an array containing all the elements of this vector
     */
    vector<Object> toArray() {

        vector<Object> newObjects;
        // Object newObjects[] = new Object[size()];
        // System.arraycopy(m_Objects, 0, newObjects, 0, size());
        return newObjects;
    }

    /**
     * Sets the vector's capacity to the given value.
     *
     * @param capacity the new capacity
     */
    void setCapacity(int capacity) {

        Object newObjects[] = new Object[capacity];

        System.arraycopy(m_Objects, 0, newObjects, 0, Math.min(capacity, m_Size));
        m_Objects = newObjects;
        if (m_Objects.length < m_Size)
            m_Size = m_Objects.length;
    }

    /**
     * Sets the element at the given index.
     *
     * @param element the element to be put into the vector
     * @param index the index at which the element is to be placed
     */
    //@ requires 0 <= index && index < size();
    void setElementAt(Object element, int index) {

        m_Objects[index] = element;
    }

    /**
     * Returns the vector's current size.
     *
     * @return the vector's current size
     */
    //@ ensures \result == m_Size;
    /*@pure@*/ int size() {

        return m_Size;
    }

    /**
     * Swaps two elements in the vector.
     *
     * @param first index of the first element
     * @param second index of the second element
     */
    //@ requires 0 <= first && first < size();
    //@ requires 0 <= second && second < size();
    void swap(int first, int second);

    /**
     * Sets the vector's capacity to its size.
     */
    void trimToSize() {

        Object newObjects[] = new Object[m_Size];

        System.arraycopy(m_Objects, 0, newObjects, 0, m_Size);
        m_Objects = newObjects;
    }

    /**
     * Returns the revision string.
     *
     * @return		the revision
     */
//    string getRevision() {
//        return RevisionUtils.extract("$Revision: 1.16 $");
//    }
};

#endif
