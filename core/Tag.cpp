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
 *    Tag.cpp
 *    Copyright (C) 1999 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

// import java.io.Serializable;

/**
 * A <code>Tag</code> simply associates a numeric ID with a string description.
 *
 * @author <a href="mailto:len@reeltwo.com">Len Trigg</a>
 * @version $Revision: 1.13 $
 */
class Tag : public RevisionHandler {
protected:
  /** for serialization. */
  // // // // // private static final long serialVersionUID = 3326379903447135320L;

  /** The ID */
  int m_ID;

  /** The unique string for this tag, doesn't have to be numeric */
  string m_IDStr;
  
  /** The descriptive text */
  string m_Readable;

public:
  /**
   * Creates a new default Tag
   *
   */
  Tag() {
    this(0, "A new tag", "A new tag", true);
  }

  /**
   * Creates a new <code>Tag</code> instance.
   *
   * @param ident the ID for the new Tag.
   * @param readable the description for the new Tag.
   */
  Tag(int ident, string readable) {
    this(ident, "", readable);
  }
  
  /**
   * Creates a new <code>Tag</code> instance.
   *
   * @param ident the ID for the new Tag.
   * @param identStr the ID string for the new Tag (case-insensitive).
   * @param readable the description for the new Tag.
   */
  Tag(int ident, string identStr, string readable) {
    this(ident, identStr, readable, true);
  }

  Tag(int ident, string identStr, string readable, bool upperCase) {
    m_ID = ident;
    if (identStr.length() == 0) {
      m_IDStr = "" + ident;
    } else {
        m_IDStr = identStr;
      if (upperCase) {
        m_IDStr = identStr.toUpperCase();
      } 
    }
    m_Readable = readable;
  }

  /**
   * Gets the numeric ID of the Tag.
   *
   * @return the ID of the Tag.
   */
  int getID() {
    return m_ID;
  }

  /**
   * Sets the numeric ID of the Tag.
   *
   * @param id the ID of the Tag.
   */
  void setID(int id) {
    m_ID = id;
  } 

  /**
   * Gets the string ID of the Tag.
   *
   * @return the string ID of the Tag.
   */
  string getIDStr() {
    return m_IDStr;
  }

  /**
   * Sets the string ID of the Tag.
   *
   * @param str the string ID of the Tag.
   */
  void setIDStr(string str) {
    m_IDStr = str;
  }

  /**
   * Gets the string description of the Tag.
   *
   * @return the description of the Tag.
   */
  string getReadable() {
    return m_Readable;
  }

  /**
   * Sets the string description of the Tag.
   *
   * @param r the description of the Tag.
   */
  void setReadable(string r) {
    m_Readable = r;
  }
  
  /**
   * returns the IDStr
   * 
   * @return the IDStr
   */
  string toString() {
    return m_IDStr;
  }
  
  /**
   * returns a list that can be used in the listOption methods to list all
   * the available ID strings, e.g.: &lt;0|1|2&gt; or &lt;what|ever&gt;
   * 
   * @param tags the tags to create the list for
   * @return a list of all ID strings
   */
  static string toOptionList(Tag[] tags) {
    String	result;
    int		i;
    
    result = "<";
    for (i = 0; i < tags.length; i++) {
      if (i > 0)
	result += "|";
      result += tags[i];
    }
    result += ">";
    
    return result;
  }
  
  /**
   * returns a string that can be used in the listOption methods to list all
   * the available options, i.e., "\t\tID = Text\n" for each option
   * 
   * @param tags the tags to create the string for
   * @return a string explaining the tags
   */
  static string toOptionSynopsis(Tag[] tags) {
    String	result;
    int		i;

    result = "";
    for (i = 0; i < tags.length; i++) {
      result += "\t\t" + tags[i].getIDStr() + " = " + tags[i].getReadable() + "\n";
    }
    
    return result;
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.13 $");
  }
};
