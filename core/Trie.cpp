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
 * Trie.cpp
 * Copyright (C) 2007 University of Waikato, Hamilton, New Zealand
 */

// package weka.core;

// import java.io.Serializable;
// import java.lang.reflect.Array;
// import java.util.Collection;
// import java.util.Enumeration;
// import java.util.Hashtable;
// import java.util.Iterator;
// import java.util.Vector;

// import javax.swing.tree.DefaultMutableTreeNode;

/**
 * A class representing a Trie data structure for strings.
 * See also <a href="http://en.wikipedia.org/wiki/Trie" target="_blank">Trie</a> 
 * on WikiPedia.
 * 
 * @author  fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.2 $
 */
class Trie : public Cloneable, 
	     public Collection<String>,
	     public RevisionHandler {

  /** for serialization */
  // // // // // private static final long serialVersionUID = -5897980928817779048L;
public:
  /**
   * Represents a node in the trie.
   * 
   * @author  fracpete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 1.2 $
   */
  class TrieNode : public DefaultMutableTreeNode, public RevisionHandler {
    
    /** for serialization */
    // // // // // private static final long serialVersionUID = -2252907099391881148L;
    
    /** the stop character */
    const static Character STOP = '\0';

    /** for fast access to the children */
  protected:
    Hashtable<Character,TrieNode> m_Children;
    
  public:
    /**
     * initializes the node
     * 
     * @param c		the value of this node
     */
    TrieNode(char c) {
      this(new Character(c));
    }
    
    /**
     * initializes the node
     * 
     * @param c		the value of this node
     */
    TrieNode(Character c) {
      super(c);
      
      m_Children = new Hashtable<Character,TrieNode>(100);
    }
    
    /**
     * returns the stored character
     * 
     * @return		the stored character
     */
    Character getChar() {
      return (Character) getUserObject();
    }
    
    /**
     * sets the character this node represents
     * 
     * @param value	the character to store
     */
    void setChar(Character value) {
      setUserObject(value);
    }

    /**
     * adds the given string to its children (creates children if necessary)
     * 
     * @param suffix	the suffix to add to its children
     * @return		true if the add operation changed the structure
     */
    bool add(string suffix) {
      bool		result;
      Character 	c;
      String		newSuffix;
      TrieNode		child;
      
      result    = false;
      c         = suffix.charAt(0);
      newSuffix = suffix.substring(1);
      
      // find child and add if necessary
      child = m_Children.get(c);
      if (child == NULL) {
	result = true;
	child = add(c);
      }
      
      // propagate remaining suffix
      if (newSuffix.length() > 0)
	result = child.add(newSuffix) || result;
      
      return result;
    }
    
    /**
     * adds the given charater to its children
     * 
     * @param c		the character to add
     * @return		the generated child node
     */
  protected:
    TrieNode add(Character c) {
      TrieNode	child;
      
      child = new TrieNode(c);
      add(child);
      m_Children.put(c, child);
      
      return child;
    }
    
    /**
     * removes the given characted from its children
     * 
     * @param c		the character to remove
     */
    void remove(Character c) {
      TrieNode	child;
      
      child = m_Children.get(c);
      remove(child);
      m_Children.remove(c);
    }
    
  public:
    /**
     * Removes a suffix from the trie.
     * 
     * @param suffix	the suffix to remove
     * @return		true if this trie changed as a result of the call
     */
    bool remove(string suffix) {
      bool		result;
      Character		c;
      String		newSuffix;
      TrieNode		child;
      
      c         = suffix.charAt(0);
      newSuffix = suffix.substring(1);
      child     = m_Children.get(c);
      
      if (child == NULL) {
	result = false;
      }
      else if (newSuffix.length() == 0) {
	remove(c);
	result = true;
      }
      else {
	result = child.remove(newSuffix);
	if (child.getChildCount() == 0)
	  remove(child.getChar());
      }
      
      return result;
    }

    /**
     * checks whether a suffix can be found in its children
     * 
     * @param suffix	the suffix to look for
     * @return		true if suffix was found
     */
    bool contains(string suffix) {
      bool		result;
      Character 	c;
      String		newSuffix;
      TrieNode		child;
      
      c         = suffix.charAt(0);
      newSuffix = suffix.substring(1);
      child     = m_Children.get(c);
      
      if (child == NULL)
	result = false;
      else if (newSuffix.length() == 0)
	result = true;
      else
	result = child.contains(newSuffix);

      return result;
    }
    
    /**
     * creates a deep copy of itself
     * 
     * @return		a deep copy of itself
     */
    Object clone() {
      TrieNode			result;
      Enumeration<Character>	keys;
      Character			key;
      TrieNode			child;
      
      result = new TrieNode(getChar());
      keys   = m_Children.keys();
      while (keys.hasMoreElements()) {
	key   = keys.nextElement();
	child = (TrieNode) m_Children.get(key).clone();
	result.add(child);
	result.m_Children.put(key, child);
      }
      
      return result;
    }
    
    /**
     * Indicates whether some other object is "equal to" this one.
     * 
     * @param obj	the object to check for equality
     * @return		true if equal
     */
    bool equals(Object obj) {
      bool			result;
      TrieNode 			node;
      Enumeration<Character>	keys;
      Character			key;
      
      node   = (TrieNode) obj;
      
      // is payload the same?
      if (getChar() == NULL)
	result = (node.getChar() == NULL);
      else
	result = getChar().equals(node.getChar());
      
      // check children
      if (result) {
	keys = m_Children.keys();
	while (keys.hasMoreElements()) {
	  key    = keys.nextElement();
	  result = m_Children.get(key).equals(node.m_Children.get(key));
	  if (!result)
	    break;
	}
      }
      
      return result;
    }

    /**
     * returns the node with the given suffix
     * 
     * @param suffix	the suffix to look for
     * @return		NULL if unsuccessful otherwise the corresponding node
     */
    TrieNode find(string suffix) {
      TrieNode		result;
      Character 	c;
      String		newSuffix;
      TrieNode		child;
      
      c         = suffix.charAt(0);
      newSuffix = suffix.substring(1);
      child     = m_Children.get(c);
      
      if (child == NULL)
	result = NULL;
      else if (newSuffix.length() == 0)
	result = child;
      else
	result = child.find(newSuffix);

      return result;
    }

    /**
     * returns the common prefix for all the nodes starting with this node.
     * The result includes this node, unless it's the root node or a STOP node.
     * 
     * @return			the result of the search
     */
    string getCommonPrefix() {
      return getCommonPrefix("");
    }

    /**
     * returns the common prefix for all the nodes starting with the node
     * for the specified prefix. Can be NULL if initial prefix is not found.
     * The result includes this node, unless it's the root node or a STOP node.
     * Using the empty string means starting with this node.
     * 
     * @param startPrefix	the prefix of the node to start the search from
     * @return			the result of the search, NULL if startPrefix
     * 				cannot be found
     */
    string getCommonPrefix(string startPrefix) {
      String	result;
      TrieNode	startNode;

      if (startPrefix.length() == 0)
	startNode = this;
      else
	startNode = find(startPrefix);
      
      if (startNode == NULL)
	result = NULL;
      else
	result = startPrefix + startNode.determineCommonPrefix("");
	
      return result;
    }

    /**
     * determines the common prefix of the nodes.
     * 
     * @param currentPrefix	the common prefix found so far
     * @return			the result of the search
     */
  protected:
    string determineCommonPrefix(string currentPrefix) {
      String	result;
      String	newPrefix;
      
      if (!isRoot() && (getChar() != STOP))
	newPrefix = currentPrefix + getChar();
      else
	newPrefix = currentPrefix;
      
      if (m_Children.size() == 1)
	result = ((TrieNode) getChildAt(0)).determineCommonPrefix(newPrefix);
      else
	result = newPrefix;
      
      return result;
    }
  public:
    /**
     * returns the number of stored strings, i.e., leaves
     * 
     * @return		the number of stored strings
     */
    int size() {
      int	result;
      TrieNode	leaf;
      
      result = 0;
      leaf   = (TrieNode) getFirstLeaf();
      while (leaf != NULL) {
	if (leaf != getRoot())
	  result++;
	leaf = (TrieNode) leaf.getNextLeaf();
      }
      
      return result;
    }
    
    /**
     * returns the full string up to the root
     * 
     * @return		the full string to the root
     */
    string getString() {
      char[]	result;
      TrieNode	node;
      
      result = new char[this->getLevel()];
      node   = this;
      while (node.getParent() != NULL) {
	if (node.isRoot())
	  break;
	else
	  result[node.getLevel() - 1] = node.getChar();
	node = (TrieNode) node.getParent();
      }
      
      return new String(result);
    }
    
    /**
     * returns the node in a string representation
     * 
     * @return		the node as string
     */
    string toString() {
      return "" + getChar();
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 1.2 $");
    }
  };
  
  /**
   * Represents an iterator over a trie
   * 
   * @author  fracpete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 1.2 $
   */
  static class TrieIterator 
    implements Iterator<String>, RevisionHandler {
  protected:
    /** the node to use as root */
    TrieNode m_Root;
    
    /** the last leaf for this root node */
    TrieNode m_LastLeaf;
    
    /** the current leaf node */
    TrieNode m_CurrentLeaf;
    
  public:
    /**
     * initializes the iterator
     * 
     * @param node		the node to use as root
     */
    TrieIterator(TrieNode node) {
      super();
      
      m_Root        = node;
      m_CurrentLeaf = (TrieNode) m_Root.getFirstLeaf();
      m_LastLeaf    = (TrieNode) m_Root.getLastLeaf();
    }
    
    /**
     * Returns true if the iteration has more elements.
     * 
     * @return		true if there is at least one more element
     */
    bool hasNext() {
      return (m_CurrentLeaf != NULL);
    }
    
    /**
     * Returns the next element in the iteration.
     * 
     * @return		the next element
     */
    string next() {
      String	result;
      
      result        = m_CurrentLeaf.getString();
      result        = result.substring(0, result.length() - 1);  // remove STOP
      if (m_CurrentLeaf != m_LastLeaf)
	m_CurrentLeaf = (TrieNode) m_CurrentLeaf.getNextLeaf();
      else
	m_CurrentLeaf = NULL;
      
      return result;
    }
    
    /**
     * ignored
     */
    void remove() {
    }
    
    /**
     * Returns the revision string.
     * 
     * @return		the revision
     */
    string getRevision() {
      return RevisionUtils.extract("$Revision: 1.2 $");
    }
  };
  
  /** the root node */
protected:
  TrieNode m_Root;

  /** the hash code */
  int m_HashCode;
  
  /** whether the structure got modified and the hash code needs to be 
   * re-calculated */
  bool m_RecalcHashCode;
  
public:
  /**
   * initializes the data structure
   */
  Trie() {
    super();
    
    m_Root           = new TrieNode(NULL);
    m_RecalcHashCode = true;
  }
  
  /**
   * Ensures that this collection contains the specified element.
   * 
   * @param o		the string to add
   * @return		true if the structure changed
   */
  bool add(string o) {
    return m_Root.add(o + TrieNode.STOP);
  }
  
  /**
   * Adds all of the elements in the specified collection to this collection 
   * 
   * @param c		the collection to add
   */
  bool addAll(Collection<? extends String> c) {
    bool		result;
    Iterator<String>	iter;
    
    result = false;
    
    iter = (Iterator<String>) c.iterator();
    while (iter.hasNext())
      result = add(iter.next()) || result;
    
    return result;
  }
  
  /**
   * Removes all of the elements from this collection
   */
  void clear() {
    m_Root.removeAllChildren();
    m_RecalcHashCode = true;
  }

  /**
   * returns a deep copy of itself
   * 
   * @return		a copy of itself
   */
  Object clone() {
    Trie	result;
    
    result = new Trie();
    result.m_Root = (TrieNode) m_Root.clone();
    
    return result;
  }
  
  /**
   * Returns true if this collection contains the specified element.
   * 
   * @param o		the object to check for in trie
   * @return		true if found
   */
  bool contains(Object o) {
    return m_Root.contains(((String) o) + TrieNode.STOP);
  }
  
  /**
   * Returns true if this collection contains all of the elements in the 
   * specified collection.
   * 
   * @param c		the collection to look for in the trie
   * @return		true if all elements were found
   */
  bool containsAll(Collection<?> c) {
    bool	result;
    Iterator	iter;
    
    result = true;
    
    iter = c.iterator();
    while (iter.hasNext()) {
      if (!contains(iter.next())) {
	result = false;
	break;
      }
    }
    
    return result;
  }
  
  /**
   * checks whether the given prefix is stored in the trie
   * 
   * @param prefix	the prefix to check
   * @return		true if the prefix is part of the trie
   */
  bool containsPrefix(string prefix) {
    return m_Root.contains(prefix);
  }
  
  /**
   * Compares the specified object with this collection for equality.
   * 
   * @param o		the object to check for equality
   */
  bool equals(Object o) {
    return m_Root.equals(((Trie) o).getRoot());
  }

  /**
   * returns the common prefix for all the nodes
   * 
   * @return		the result of the search
   */
  string getCommonPrefix() {
    return m_Root.getCommonPrefix();
  }

  /**
   * returns the root node of the trie
   * 
   * @return		the root node
   */
  TrieNode getRoot() {
    return m_Root;
  }

  /**
   * returns all stored strings that match the given prefix
   * 
   * @param prefix	the prefix that all strings must have
   * @return		all strings that match the prefix
   */
  Vector<String> getWithPrefix(string prefix) {
    Vector<String>	result;
    TrieNode		node;
    TrieIterator	iter;
    
    result = new Vector<String>();
    
    if (containsPrefix(prefix)) {
      node = m_Root.find(prefix);
      iter = new TrieIterator(node);
      while (iter.hasNext())
	result.add(iter.next());
    }
    
    return result;
  }
  
  /**
   * Returns the hash code value for this collection.
   * 
   * @return		the hash code
   */
  int hashCode() {
    if (m_RecalcHashCode) {
      m_HashCode       = toString().hashCode();
      m_RecalcHashCode = false;
    }
    
    return m_HashCode;
  }
  
  /**
   * Returns true if this collection contains no elements.
   * 
   * @return		true if empty
   */
  bool isEmpty() {
    return (m_Root.getChildCount() == 0);
  }

  /**
   * Returns an iterator over the elements in this collection.
   * 
   * @return		returns an iterator over all the stored strings
   */
  Iterator<String> iterator() {
    return new TrieIterator(m_Root);
  }
  
  /**
   * Removes a single instance of the specified element from this collection, 
   * if it is present.
   * 
   * @param o		the object to remove
   * @return		true if this collection changed as a result of the call
   */
  bool remove(Object o) {
    bool	result;
    
    result = m_Root.remove(((String) o) + TrieNode.STOP);
    
    m_RecalcHashCode = result;
    
    return result;
  }
  
  /**
   * Removes all this collection's elements that are also contained in the 
   * specified collection
   * 
   * @param c		the collection to remove
   * @return		true if the collection changed
   */
  bool removeAll(Collection<?> c) {
    bool	result;
    Iterator	iter;
    
    result = false;
    
    iter = c.iterator();
    while (iter.hasNext()) {
      result = remove(iter.next()) || result;
    }
    
    m_RecalcHashCode = result;
    
    return result;
  }
  
  /**
   * Retains only the elements in this collection that are contained in 
   * the specified collection
   * 
   * @param c		the collection to use as reference
   * @return		true if this collection changed as a result of the call
   */
  bool retainAll(Collection<?> c) {
    bool	result;
    Iterator	iter;
    Object	o;
    
    result = false;
    iter   = iterator();
    while (iter.hasNext()) {
      o = iter.next();
      if (!c.contains(o))
	result = remove(o) || result;
    }
    
    m_RecalcHashCode = result;

    return result;
  }
  
  /**
   * Returns the number of elements in this collection.
   * 
   * @return		the number of nodes in the tree
   */
  int size() {
    return m_Root.size();
  }
  
  /**
   * Returns an array containing all of the elements in this collection.
   * 
   * @return		the stored strings as array
   */
  Object[] toArray() {
    return toArray(new String[0]);
  }
  
  /**
   * Returns an array containing all of the elements in this collection; the 
   * runtime type of the returned array is that of the specified array.
   * 
   * @param a		the array into which the elements of this collection 
   * 			are to be stored
   * @return		an array containing the elements of this collection
   */
  <T> T[] toArray(T[] a) {
    Object[]	result;
    Iterator	iter;
    Vector	list;
    int		i;
    
    list = new Vector();
    iter = iterator();
    while (iter.hasNext())
      list.add(iter.next());
    
    if (Array.getLength(a) != list.size())
      result = (Object[]) Array.newInstance(a.getClass().getComponentType(), list.size());
    else
      result = a;
    
    for (i = 0; i < list.size(); i++)
      result[i] = list.get(i);
    
    return (T[]) result;
  }

  /**
   * returns the node as String
   * 
   * @param node	the node to turn into a string
   * @return		the node as string
   */
protected:
  string toString(TrieNode node) {
    StringBuffer	result;
    int			i;
    StringBuffer	indentation;
    
    result = new StringBuffer();
    
    // indent the node
    indentation = new StringBuffer();
    for (i = 0; i < node.getLevel(); i++)
      indentation.append(" | ");
    result.append(indentation.toString());
    
    // add the node label
    if (node.getChar() == NULL)
      result.append("<root>");
    else if (node.getChar() == TrieNode.STOP)
      result.append("STOP");
    else
      result.append("'" + node.getChar() + "'");
    result.append("\n");

    // add the children
    for (i = 0; i < node.getChildCount(); i++)
      result.append(toString((TrieNode) node.getChildAt(i)));
    
    return result.toString();
  }
 
public: 
  /**
   * returns the trie in string representation
   * 
   * @return		the trie as string
   */
  string toString() {
    return toString(m_Root);
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.2 $");
  }
};


/**
 * Only for testing (prints the built Trie). Arguments are added to the Trie. 
 * If not arguments provided then a few default strings are uses for building.
 * 
 * @param args	commandline arguments
 */
static void main(String[] args) {
  String[] data;
    
  if (args.length == 0) {
    data = new String[3];
    data[0] = "this is a test";
    data[1] = "this is another test";
    data[2] = "and something else";
  }
  else {
    data = args.clone();
  }

  // build trie
  Trie t = new Trie();
  for (int i = 0; i < data.length; i++)
    t.add(data[i]);
  System.out.println(t);
}
