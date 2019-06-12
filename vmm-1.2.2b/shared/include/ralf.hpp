//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//
#ifndef RALF_HPP
#define RALF_HPP

#include <string>
#include <list>
#include <map>
#include <stdexcept>
#include <iostream>
#include <cstdlib>


/**
 * Macro for disabling copy and assignment operation, wherever
 * required.
 */
#define RALF_DISABLE_COPY_AND_ASSIGN(classname)                      \
  /**                                                                \
   * Disabling Copy Constructor.                                     \
   */                                                                \
   classname(const classname & cpy);                                 \
                                                                     \
  /**                                                                \
   * Disabling Assignment Operator.                                  \
   */                                                                \
   classname & operator=(const classname & cpy);                     


#define RALF_DISABLE_ASSIGN(classname)                               \
  /**                                                                \
   * Disabling Assignment Operator.                                  \
   */                                                                \
   classname & operator=(const classname & cpy);


/**
 * 'namespace' encapsulating RAL C++ API(s).
 */
namespace ralf {

/**
 * Top level RALF exception and error handling base class.
 */ 
class vmm_ralf_exception : public std::exception {
public:
  /**
   * Default Constructor.
   *
   * @param msg Exception message, if any.
   */
   explicit vmm_ralf_exception(const char * msg = NULL);

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_exception() throw();

  /**
   * Gets the exception message.
   *
   * @return Const Reference to Exception Message
   */
   virtual const std::string & getMessage() const throw();

private:
   std::string msg_;  
};


/**
 * Top level RALF error handling base class.
 */ 
class vmm_ralf_error : public vmm_ralf_exception {
public:
  /**
   * Default Constructor.
   *
   * @param error_msg Error message, if any.
   */
   explicit vmm_ralf_error(const char * error_msg = NULL);
};


/**
 * RALF Exception Class for errors of type 'invalid operation performed'.
 */ 
class vmm_ralf_invalid_oprn : public vmm_ralf_error {
public:
  /**
   * Default Constructor.
   *
   * @param why: Reason for which the operation is getting 
   *               considered 'invalid'.
   */
   explicit vmm_ralf_invalid_oprn(const char * why = NULL);
};



/**
 * Descriptor of RALF hdl_path specification.
 */
class vmm_ralf_hdl_path {
public:
  /**
   * Virtual Desctructor.
   */
   virtual ~vmm_ralf_hdl_path() {}

  /**
   * HdlPath Iterator Class.
   */
   class const_hdl_path_iter {
   public:
     /**
      * Virtual Desructor.
      */
      virtual ~const_hdl_path_iter() {}
   
     /**
      * Prefix increment operator.
      *
      * @return Reference to the incremented iterator itself.
      */
      virtual const_hdl_path_iter & operator++() = 0;
   
     /**
      * Overloading de-reference operator.
      *
      * @return Returns the contained sequence element
      *         currently pointed by the iterator.
      */
      virtual const std::string * operator*() const = 0;
   
     /**
      * Checks if the iterator is pointing to the first 
      * element i.e. begining of the sequence.
      *
      * @return Returns true if the iterator is pointing to
      *         the first element. Else returns false.
      */
      virtual bool isBegin() const = 0;
   
     /**
      * Checks if the iterator is pointing to the end (i.e. one 
      * past last element) of the sequence.
      *
      * @return Returns true if the iterator is pointing to the end.
      *         Else returns false.
      */
      virtual bool isEnd() const = 0;
   };
   
  /**
   * Gets the hdl_path iterator.
   *
   * Assumes the following concatenated implementation of the
   * hdl_path:
   *     { <sub_hdl_path1>, <sub_hdl_path2>, ..., <sub_hdl_pathN> }
   * So, returns iterator to the list of all the sub_hdl_path(s).
   *
   * The sequence of hdl_path(s) maintained in the returned iterator would
   * be same as specified in the RALF file i.e. from left to right.
   *
   * @return Pointer to a newly created iterator object. The returned
   *         iterator is initialized to point to the first/left-most
   *         sub_hdl_path.
   *         The returned iterator object would need to be deleted
   *         by the user using 'delete', after using it.
   */
   virtual const_hdl_path_iter * createHdlPathIter() const = 0;

  /**
   * Checks if the target variable/signal of the hdl_path has
   * been implemented in VHDL.
   *
   * Verilog implementation is assumed by default.
   *
   * @return 'true' if implemented in VHDL, else 'false'.
   */
   virtual bool isVhdlPath() const = 0;
};




/**
 * Descriptor of RALF 'constraint' specification.
 */
class vmm_ralf_constraint {
public:
  /**
   * Virtual Desctructor.
   */
   virtual ~vmm_ralf_constraint() {}

  /**
   * Gets the name of the constraint.
   *
   * @return Const Reference to the constraint name.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the body of the constraint.
   *
   * @return Const Reference to the constraint body.
   */
   virtual const std::string & getBody() const = 0;
};



/**
 * Descriptor of a RALF 'field' type.
 */
class vmm_ralf_fld_typ {
public:
  /**
   * Descriptor of RALF supported field 'access' types.
   */
   enum access_e {
      RW,
      RO,
      WO,
      W1,
      RU,
      RC,
      W1C,
      A0,
      A1,
      DC,
      OTHER,
      USER0,
      USER1,
      USER2,
      USER3
   };


  /**
   * Virtual Desctructor.
   */
   virtual ~vmm_ralf_fld_typ() {}

  /**
   * Gets the name of the RALF 'field' type.
   *
   * @return Const Reference to the name of the RALF 'field' type.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the field size in bits.
   *
   * @return Field size in bits.
   */
   virtual const size_t & getNBits() const = 0;

  /**
   * Gets the field 'access' specification.
   *
   * @return Enumeration constant of type 'access_e' to indicate 
   *         the field 'access' specification. 
   */
   virtual access_e getAccess() const = 0;

  /**
   * Gets the Hard Reset value of the field.
   *
   * @return Const Reference to the hard reset value of the field.
   */
   virtual const std::string & getHardReset() const = 0;

  /**
   * Gets the Soft Reset value of the field.
   *
   * @return Const Reference to the soft reset value of the field.
   */
   virtual const std::string & getSoftReset() const = 0;

  /**
   * Gets the constraint, if any specified, in the corresponding 
   * RALF description.
   *
   * @return Pointer to the const constraint data structure, if the 
   *         constraint has been specified in the corresponding RALF 
   *         description. Else returns NULL.
   */
   virtual const vmm_ralf_constraint * getConstraint() const = 0;
};



/**
 * RALF descriptor of an instantiated field, as instantiated in a register. 
 */
class vmm_ralf_fld_instance {
public:
  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_fld_instance() {}

  /**
   * Gets the instance name.
   *
   * @return Const Reference to the instance name.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the corresponding RALF type.
   *
   * @return Const Reference to the corresponding RALF type.
   */
   virtual const vmm_ralf_fld_typ & getType() const = 0;

  /**
   * Gets the hdl_path, if any specified, in the corresponding
   * RALF description.
   *
   * @return Pointer to the const hdl_path data structure, if
   *         the hdl_path has been specified in the corresponding
   *         RALF description. Else returns NULL.
   */
   virtual const vmm_ralf_hdl_path * getHdlPath() const = 0;

  /**
   * Gets the LSB position of the field in the parent register.
   *
   * @return Const Reference to the LSB position of the field instance. 
   */
   virtual const size_t & getLSBPosition() const = 0;
};


/**
 * RALF descriptor of a 'register' type.
 */
class vmm_ralf_reg_typ {
public:
  /**
   * Field Iterator Class.
   */
   class const_fld_iter {
   public:
     /**
      * Virtual Desructor.
      */
      virtual ~const_fld_iter() {}
   
     /**
      * Prefix increment operator.
      *
      * @return Reference to the incremented iterator itself.
      */
      virtual const_fld_iter & operator++() = 0;
   
     /**
      * Overloading de-reference operator.
      *
      * @return Returns the contained sequence element
      *         currently pointed by the iterator.
      */
      virtual const vmm_ralf_fld_instance * operator*() const = 0;
   
     /**
      * Checks if the iterator is pointing to the first 
      * element i.e. begining of the sequence.
      *
      * @return Returns true if the iterator is pointing to the
      *         the first element. Else returns false.
      */
      virtual bool isBegin() const = 0;
   
     /**
      * Checks if the iterator is pointing to the end (i.e. one 
      * past last element) of the sequence.
      *
      * @return Returns true if the iterator is pointing to the end.
      *         Else returns false.
      */
      virtual bool isEnd() const = 0;
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_reg_typ() {}

  /**
   * Gets the name of the RALF 'register' type.
   *
   * @return Const Reference to the name of the RALF 'register' type.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the scope name of the RALF 'register' type.
   *
   * @return Const Reference to the scope name of the RALF 'register' type.
   */
   virtual const std::string & getScopeName() const = 0;

  /**
   * Gets the size of the register in bytes.
   *
   * @return Const Reference to the size of the register (in bytes).
   */
   virtual const size_t & getNBytes() const = 0;

  /**
   * Gets an iterator to iterate over the list of all field 
   * instances in the register.
   *
   * @return Pointer to a newly created iterator object. The returned
   *         iterator is initialized to point to the first field 
   *         instance.
   *         The returned iterator object would need to be deleted
   *         by the user using 'delete', after using it.
   */
   virtual const_fld_iter * createFldIter() const = 0;

  /**
   * Checks if alignment of field instances in the register is from 
   * left(MSB) to right(LSB). 
   *
   * @return 'true' if yes, else 'false' 
   */
   virtual bool isLeft2Right() const = 0;

  /**
   * Checks if the register is sharable among multiple domains of a block.
   *
   * @return 'true' if sharable, else 'false'.
   */
   virtual bool isShared() const = 0;

  /**
   * Gets the constraint, if any specified, in the corresponding RALF 
   * description.
   *
   * @return Pointer to the const constraint data structure, if the 
   *         constraint has been specified in the corresponding RALF 
   *         description. Else returns NULL.
   */
   virtual const vmm_ralf_constraint * getConstraint() const = 0;

  /**
   * Gets the shared hdl_path, if any specified, in the corresponding RALF 
   * description. 
   *
   * Throws exception vmm_ralf_invalid_oprn() if this method is incoked for 
   * a register that is not shared.
   *
   * @return Pointer to const hdl_path data structure, if shared hdl_path 
   *         has been specified 
   *         in the corresponding RALF description. Else returns NULL.
   */
   virtual const vmm_ralf_hdl_path * 
      getSharedHdlPath() const throw(vmm_ralf_invalid_oprn) = 0;
};


/**
 * Abstract/Common Base class of all *direct* structural components of 
 * RALF 'block'.
 *
 * Note: *direct* structural components of RALF 'block' are 'register', 
 *       'memory', 'virtual register' and 'regfile'. 'field' is not a 
 *       *direct* structural component of block as it cannot be directly
 *       instantiated (structurally) inside a block.
 */
class vmm_ralf_blk_component_instance {
public:
  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_blk_component_instance() {}

  /**
   * Gets the instance name.
   *
   * @return Const Reference to the instance name.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the hdl_path, if any specified, in the corresponding
   * RALF description.
   *
   * @return Pointer to the const hdl_path data structure, if
   *         the hdl_path has been specified in the corresponding
   *         RALF description. Else returns NULL.
   */
   virtual const vmm_ralf_hdl_path * getHdlPath() const = 0;

  /**
   * Gets the offset/address of the instance in the parent
   * RALF Construct/Type.
   *
   * @return Const Reference to the offset/address.
   */
   virtual const size_t & getOffset() const = 0;

  /**
   * Gets the address space size of the instance in the parent 
   * regfile/block domain.
   *
   * @return Const Reference to the address space size.
   */
   virtual const size_t & getAddrSpaceSize() const = 0;
};


/**
 * RALF descriptor of an instantiated register, as instantiated in a 
 * regfile or block.
 */
class vmm_ralf_reg_instance : public virtual vmm_ralf_blk_component_instance {
public:
  /**
   * Descriptor of RALF supported shared register instance 'access' 
   * specification types.
   */
   enum shared_access_e {
      DEFAULT,    //!< Defauilt is RW shared access.
      READ,
      WRITE
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_reg_instance() {}

  /**
   * Gets the corresponding RALF type.
   *
   * @return Const Reference to the corresponding RALF type.
   */
   virtual const vmm_ralf_reg_typ & getType() const = 0;

  /**
   * Checks if the instance is an array instance.
   *
   * @return 'true' if yes, else 'false'.
   */
   virtual bool isArray() const = 0;

  /**
   * Gets the size of the array.
   *
   * Throws exception vmm_ralf_invalid_oprn if this method is invoked on a 
   * non-array instance.
   *
   * @return Const Reference to the size of the array.
   */
   virtual const size_t & 
      getArraySize() const throw(vmm_ralf_invalid_oprn) = 0;

  /**
   * Gets the array increment.
   *
   * Throws exception vmm_ralf_invalid_oprn if this method is invoked on a 
   * non-array instance.
   *
   * @return Const Reference to the array increment.
   */
   virtual const size_t & 
      getArrayIncr() const throw(vmm_ralf_invalid_oprn) = 0;


  /**
   * Checks if the register instance is un-mapped in the parent block 
   * domain/regfile.
   *
   * @return 'true' if unmapped, else 'false'.
   */
   virtual bool isUnMapped() const = 0;

  /**
   * Gets the offset/address of the instance in the parent
   * RALF Construct/Type.
   *
   * Throws exception 'vmm_ralf_invalid_oprn' if this method is 
   * invoked on an un-mapped register instance.
   *
   * @return Const Reference to the offset/address.
   */
   virtual const size_t & getOffset() const throw(vmm_ralf_invalid_oprn) = 0;

  /** 
   * Gets the shared access specification of the shared register instance.   
   *
   * @return Enumeration constant of type 'shared_access_e' to indicate 
   * access specification.
   */
   virtual shared_access_e 
      getSharedAccess() const throw(vmm_ralf_invalid_oprn) = 0;

};



/**
 * RALF descriptor of 'regfile' type.
 */
class vmm_ralf_rfile_typ {
public:
  /**
   * Register Iterator Class.
   */
   class const_reg_iter {
   public:
     /**
      * Virtual Desructor.
      */
      virtual ~const_reg_iter() {}
   
     /**
      * Prefix increment operator.
      *
      * @return Reference to the incremented iterator itself.
      */
      virtual const_reg_iter & operator++() = 0;
   
     /**
      * Overloading de-reference operator.
      *
      * @return Returns the contained sequence element
      *         currently pointed by the iterator.
      */
      virtual const vmm_ralf_reg_instance * operator*() const = 0;
   
     /**
      * Checks if the iterator is pointing to the first 
      * element i.e. begining of the sequence.
      *
      * @return Returns true if the iterator is pointing to the
      *         the first element. Else returns false.
      */
      virtual bool isBegin() const = 0;
   
     /**
      * Checks if the iterator is pointing to the end (i.e. one 
      * past last element) of the sequence.
      *
      * @return Returns true if the iterator is pointing to the end.
      *         Else returns false.
      */
      virtual bool isEnd() const = 0;
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_rfile_typ() {}

  /**
   * Gets the name of the RALF construct.
   *
   * @return Const Reference to the name of the RALF construct.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the scope name of the RALF construct.
   *
   * @return Const Reference to the scope name of the RALF construct.
   */
   virtual const std::string & getScopeName() const = 0;

  /**
   * Gets an iterator to iterate over the list of all register
   * instances in the register file.
   *
   * @return Pointer to a newly created iterator object. The returned
   *         iterator is initialized to point to the first register 
   *         instance.
   *         The returned iterator object would need to be deleted
   *         by the user using 'delete', after using it.
   */
   virtual const_reg_iter * createRegIter() const = 0;


  /**
   * Gets the constraint, if any specified, in the corresponding RALF 
   * description.
   *
   * @return Pointer to the const constraint data structure, if the 
   *         constraint has been specified in the corresponding RALF
   *         description. Else returns NULL.
   */
   virtual const vmm_ralf_constraint * getConstraint() const = 0;
};



/**
 * RALF descriptor of an instantiated file, as instantiated in a block.
 */
class vmm_ralf_rfile_instance : public virtual vmm_ralf_blk_component_instance {
public:
  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_rfile_instance() {}

  /**
   * Gets the corresponding RALF type.
   *
   * @return Const Reference to the corresponding RALF type.
   */
   virtual const vmm_ralf_rfile_typ & getType() const = 0;

  /**
   * Checks if the instance is an array instance.
   *
   * @return 'true' if yes, else 'false'.
   */
   virtual bool isArray() const = 0;

  /**
   * Gets the size of the array.
   *
   * Throws exception vmm_ralf_invalid_oprn if this method is invoked on a 
   * non-array instance.
   *
   * @return Const Reference to the size of the array.
   */
   virtual const size_t & 
      getArraySize() const throw(vmm_ralf_invalid_oprn) = 0;

  /**
   * Gets the array increment.
   *
   * Throws exception vmm_ralf_invalid_oprn if this method is invoked on a 
   * non-array instance.
   *
   * @return Const Reference to the array increment.
   */
   virtual const size_t & 
      getArrayIncr() const throw(vmm_ralf_invalid_oprn) = 0;

};


/**
 * RALF descriptor of a 'memory' type.
 */
class vmm_ralf_mem_typ {
public:
  /**
   * Descriptor of RALF supported memory 'access' types.
   */
   enum access_e {
      RW,         //!< Corresponds to RAM
      RO          //!< Corresponds to ROM
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_mem_typ() {}

  /**
   * Gets the name of the RALF construct.
   *
   * @return Const Reference to the name of the RALF construct.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the scope name of the RALF construct.
   *
   * @return Const Reference to the scope name of the RALF construct.
   */
   virtual const std::string & getScopeName() const = 0;

  /**
   * Gets the size (number of addressable locations) in the memory.
   *
   * @return Const Reference to the size of the memory.
   */
   virtual const size_t & getSize() const = 0;

  /**
   * Gets the number bits in each memory location.
   *
   * @return Const Reference to 'number bits in each memory location'.
   */
   virtual const size_t & getNBits() const = 0;

  /**
   * Gets the 'access' specification of the memory.
   *
   * @return Enumeration constant of type 'access_e' to indicate
   *         if the memory is a RAM or ROM.
   */
   virtual access_e getAccess() const = 0;

  /**
   * Checks if the memory is sharable among multiple domains of a block.
   *
   * @return 'true' if sharable, else 'false'.
   */
   virtual bool isShared() const = 0;

  /**
   * Gets the shared hdl_path, if any specified, in the corresponding 
   * RALF description.
   *
   * @return Pointer to const hdl_path data structure, if shared hdl_path 
   *         has been specified
   *         in the corresponding RALF description. Else returns NULL.
   */
   virtual const vmm_ralf_hdl_path * getSharedHdlPath() const = 0;
};



/**
 * RALF descriptor of an instantiated memory, as instantiated in a block.
 */
class vmm_ralf_mem_instance : public virtual vmm_ralf_blk_component_instance {
public:
  /**
   * Descriptor of RALF supported shared memory instance 'access' 
   * specification types.
   */
   enum shared_access_e {
      DEFAULT,    //!< Default is RW shared access.
      READ,
      WRITE
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_mem_instance() {}

  /**
   * Gets the corresponding RALF type.
   *
   * @return Const Reference to the corresponding RALF type.
   */
   virtual const vmm_ralf_mem_typ & getType() const = 0;

  /**
   * Checks if the memory instance is un-mapped in the parent block domain.
   *
   * @return 'true' if unmapped, else 'false'.
   */
   virtual bool isUnMapped() const = 0;

  /**
   * Gets the offset/address of the memory instance in the parent block 
   * domain.
   *
   * Throws exception vmm_ralf_invalid_oprn if the memory instance is 
   * unmapped.
   *
   * @return Const Reference to the offset/address of the memory instance in
   *         the parent block domain.
   */
   virtual const size_t & getOffset() const throw(vmm_ralf_invalid_oprn) = 0;

  /**
   * Gets the shared access specification of the shared memory instance.
   *
   * @return Enumeration constant of type 'shared_access_e' to indicate 
   *         access specification.
   */
   virtual shared_access_e 
      getSharedAccess() const throw(vmm_ralf_invalid_oprn) = 0;
};


/**
 * Abstract base class of RALF block and system domain descriptors.
 */
class vmm_ralf_domain {
public:
  /**
   * Descriptor of RALF supported 'endian' types.
   */
   enum endianness_e {
      RALF_NO_ENDIAN,
      RALF_LITTLE_ENDIAN,
      RALF_BIG_ENDIAN,
      RALF_LITTLE_FIFO,
      RALF_BIG_FIFO
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_domain() {} 

  /**
   * Gets the domain width in bytes. 
   *
   * @return Const Reference to the domain width. 
   */
   virtual const size_t & getNBytes() const = 0;

  /**
   * Gets the name of the domain.
   *
   * @return Const Reference to the name of the domain. 
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the endian-ness, if any specified. 
   *
   * @return Enumeration constant of type 'endianness_e' to
   *         indicate domain's 'endian' specification. 
   */
   virtual endianness_e getEndian() const = 0;

  /**
   * Gets the constraint, if any specified, in the corresponding RALF 
   * description.
   *
   * @return Pointer to the const constraint data structure, if the 
   *         constraint has been specified in the corresponding RALF
   *         description. Else returns NULL.
   */
   virtual const vmm_ralf_constraint * getConstraint() const = 0;
};


/**
 * RALF descriptor of a block domain.
 */
class vmm_ralf_blk_domain : public virtual vmm_ralf_domain {
public:
  /**
   * Block Component Iterator Class.
   */
   class const_component_iter {
   public:
     /**
      * Virtual Desructor.
      */
      virtual ~const_component_iter() {}
   
     /**
      * Prefix increment operator.
      *
      * @return Reference to the incremented iterator itself.
      */
      virtual const_component_iter & operator++() = 0;
   
     /**
      * Overloading de-reference operator.
      *
      * @return Returns the contained sequence element
      *         currently pointed by the iterator.
      */
      virtual const vmm_ralf_blk_component_instance * 
         operator*() const = 0;
   
     /**
      * Checks if the iterator is pointing to the first 
      * element i.e. begining of the sequence.
      *
      * @return Returns true if the iterator is pointing to the
      *         the first element. Else returns false.
      */
      virtual bool isBegin() const = 0;
   
     /**
      * Checks if the iterator is pointing to the end (i.e. one 
      * past last element) of the sequence.
      *
      * @return Returns true if the iterator is pointing to the end.
      *         Else returns false.
      */
      virtual bool isEnd() const = 0;
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_blk_domain() {}

  /**
   * Gets an iterator to iterate over the list of all block
   * component instances in the block domain.
   *
   * @return Pointer to a newly created iterator object. The returned
   *         iterator is initialized to point to the first block 
   *         component instance.
   *         The returned iterator object would need to be deleted
   *         by the user using 'delete', after using it.
   */
   virtual const_component_iter * createComponentIter() const = 0;
};

/**
 * Abstract base class for RALF descriptors of block and system type.
 */
class vmm_ralf_blk_or_sys_typ {
public:
  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_blk_or_sys_typ() {}

  /**
   * Gets the name of the RALF construct.
   *
   * @return Const Reference to the name of the RALF construct.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the scope name of the RALF construct.
   *
   * @return Const Reference to the scope name of the RALF construct.
   */
   virtual const std::string & getScopeName() const = 0;
};


/**
 * RALF descriptor of block type.
 */
class vmm_ralf_blk_typ : public virtual vmm_ralf_blk_or_sys_typ {
public:
  /**
   * Block Domain Iterator Class.
   */
   class const_domain_iter {
   public:
     /**
      * Virtual Desructor.
      */
      virtual ~const_domain_iter() {}
   
     /**
      * Prefix increment operator.
      *
      * @return Reference to the incremented iterator itself.
      */
      virtual const_domain_iter & operator++() = 0;
   
     /**
      * Overloading de-reference operator.
      *
      * @return Returns the contained sequence element
      *         currently pointed by the iterator.
      */
      virtual const vmm_ralf_blk_domain * operator*() const = 0;
   
     /**
      * Checks if the iterator is pointing to the first 
      * element i.e. begining of the sequence.
      *
      * @return Returns true if the iterator is pointing to the
      *         the first element. Else returns false.
      */
      virtual bool isBegin() const = 0;
   
     /**
      * Checks if the iterator is pointing to the end (i.e. one 
      * past last element) of the sequence.
      *
      * @return Returns true if the iterator is pointing to the end.
      *         Else returns false.
      */
      virtual bool isEnd() const = 0;
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_blk_typ() {}

  /**
   * Gets an iterator to iterate over the list of all domains
   * in the block.
   *
   * @return Pointer to a newly created iterator object. The returned
   *         iterator is initialized to point to the first block
   *         domain.
   *         The returned iterator object would need to be deleted
   *         by the user using 'delete', after using it.
   */
   virtual const_domain_iter * createDomainIter() const = 0;
};


/**
 * Abstract base class descriptor of a block/system domain instance,
 * as instantiated in the parent system.
 */
class vmm_ralf_domain_instance {
public:
  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_domain_instance() {}

  /**
   * Gets the instance name.
   *
   * @return Const Reference to the instance name.
   */
   virtual const std::string & getName() const = 0;

  /**
   * Gets the hdl_path, if any specified, in the corresponding
   * RALF description.
   *
   * @return Pointer to the const hdl_path data structure, if
   *         the hdl_path has been specified in the corresponding
   *         RALF description. Else returns NULL.
   */
   virtual const vmm_ralf_hdl_path * getHdlPath() const = 0;

  /**
   * Gets the name of the instantiated domain.
   *
   * @return Const Reference to the name of the instantiated domain.
   */
   virtual const std::string & getInstantiatedDomainName() const = 0;

  /**
   * Checks if the instance is an array instance.
   *
   * @return 'true' if yes, else 'false'.
   */
   virtual bool isArray() const = 0;

  /**
   * Gets the size of the array.
   *
   * Throws exception vmm_ralf_invalid_oprn if this method is invoked on a 
   * non-array instance.
   *
   * @return Const Reference to the size of the array.
   */
   virtual const size_t & 
      getArraySize() const throw(vmm_ralf_invalid_oprn) = 0;

  /**
   * Gets the array increment.
   *
   * Throws exception vmm_ralf_invalid_oprn if this method is invoked on a 
   * non-array instance.
   *
   * @return Const Reference to the array increment.
   */
   virtual const size_t & 
      getArrayIncr() const throw(vmm_ralf_invalid_oprn) = 0;

  /**
   * Gets the offset/address of the domain instance in the parent 
   * system domain.
   *
   * @return Const Reference to the offset/address.
   */
   virtual const size_t & getOffset() const = 0;


  /**
   * Gets the address space size of the domain instance in the parent 
   * system domain.
   *
   * @return Const Reference to the address space size.
   */
   virtual const size_t & getAddrSpaceSize() const = 0;
};


/**
 * RALF descriptor of a block domain instance, as 
 * instantiated in the parent system.
 */
class vmm_ralf_blk_domain_instance : public virtual vmm_ralf_domain_instance {
public:
  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_blk_domain_instance() {}

  /**
   * Gets the corresponding RALF type.
   *
   * @return Const Reference to the corresponding RALF type.
   */
   virtual const vmm_ralf_blk_typ & getType() const = 0;
};


/**
 * RALF descriptor of a system domain.
 */
class vmm_ralf_sys_domain : public virtual vmm_ralf_domain {
public:

  /**
   * System Component Iterator Class.
   */
   class const_component_iter {
   public:
     /**
      * Virtual Desructor.
      */
      virtual ~const_component_iter() {}
   
     /**
      * Prefix increment operator.
      *
      * @return Reference to the incremented iterator itself.
      */
      virtual const_component_iter & operator++() = 0;
   
     /**
      * Overloading de-reference operator.
      *
      * @return Returns the contained sequence element
      *         currently pointed by the iterator.
      */
      virtual const vmm_ralf_domain_instance * operator*() const = 0;
   
     /**
      * Checks if the iterator is pointing to the first 
      * element i.e. begining of the sequence.
      *
      * @return Returns true if the iterator is pointing to the
      *         the first element. Else returns false.
      */
      virtual bool isBegin() const = 0;
   
     /**
      * Checks if the iterator is pointing to the end (i.e. one 
      * past last element) of the sequence.
      *
      * @return Returns true if the iterator is pointing to the end.
      *         Else returns false.
      */
      virtual bool isEnd() const = 0;
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_sys_domain() {}

  /**
   * Gets an iterator to iterate over the list of all domain
   * instances in the parent system domain.
   *
   * @return Pointer to a newly created iterator object. The returned
   *         iterator is initialized to point to the first domain
   *         instance.
   *         The returned iterator object would need to be deleted
   *         by the user using 'delete', after using it.
   */
   virtual const_component_iter * createComponentIter() const = 0;
};


/**
 * RALF descriptor of system type.
 */
class vmm_ralf_sys_typ : public virtual vmm_ralf_blk_or_sys_typ {
public:
  /**
   * System Domain Iterator Class.
   */
   class const_domain_iter {
   public:
     /**
      * Virtual Desructor.
      */
      virtual ~const_domain_iter() {}
   
     /**
      * Prefix increment operator.
      *
      * @return Reference to the incremented iterator itself.
      */
      virtual const_domain_iter & operator++() = 0;
   
     /**
      * Overloading de-reference operator.
      *
      * @return Returns the contained sequence element
      *         currently pointed by the iterator.
      */
      virtual const vmm_ralf_sys_domain * operator*() const = 0;
   
     /**
      * Checks if the iterator is pointing to the first 
      * element i.e. begining of the sequence.
      *
      * @return Returns true if the iterator is pointing to the
      *         the first element. Else returns false.
      */
      virtual bool isBegin() const = 0;
   
     /**
      * Checks if the iterator is pointing to the end (i.e. one 
      * past last element) of the sequence.
      *
      * @return Returns true if the iterator is pointing to the end.
      *         Else returns false.
      */
      virtual bool isEnd() const = 0;
   };

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_sys_typ() {}

  /**
   * Gets an iterator to iterate over the list of all domains
   * in the system.
   *
   * @return Pointer to a newly created iterator object. The returned
   *         iterator is initialized to point to the first system domain.
   *         The returned iterator object would need to be deleted
   *         by the user using 'delete', after using it.
   */
   virtual const_domain_iter * createDomainIter() const = 0;
};

/**
 * RALF descriptor of a system domain instance, as 
 * instantiated in the parent system.
 */
class vmm_ralf_sys_domain_instance : public virtual vmm_ralf_domain_instance {
public:
  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf_sys_domain_instance() {}

  /**
   * Gets the corresponding RALF type.
   *
   * @return Const Reference to the corresponding RALF type.
   */
   virtual const vmm_ralf_sys_typ & getType() const = 0;
};






/**
 * Top level concrete class whose object should be instantiated by the 
 * end user.
 *
 * Top level concrete class whose object should be instantiated by the 
 * end user, for using RALF C++ API(s) or SNPS's version of RALF to RTL
 * generator.
 */
class vmm_ralf {
public:
  /**
   * Constructor.
   *
   * Top level constructor end-users would need to use.
   *
   * @param ralf_file Unix absolute/relative RALF file name.
   * @param top       Top level block/system's name that needs to be 
   *                  accessed using the C++ API. Same as what is specified
   *                  with the '-t' option of ralgen.
   * @param rtl_dir   Dir where the RTL code should be generated. Defaults 
   *                  to current directory.
   * @param inc_dirs  Include path for 'source'd RALF files. Same as what 
   *                  can be specified using ralgen's '-I' option.
   * @quiet_mode      If set to 'true', all ralgen warnings will be suppressed.
   *                  Same as what is specified using ralgen's '-q' option.
   */
   vmm_ralf(const char * ralf_file,
            const char * top,
            const char * rtl_dir = "./",
            const char * inc_dirs = NULL,
            bool quiet_mode = false);

  /**
   * Virtual Destructor.
   */
   virtual ~vmm_ralf();


  /**
   * SNPS's Version of RALF to RTL Code Generator.
   */
   virtual void generateRTL() const;

  /**
   * Gets the top level block or system data structure (as per 'top' 
   * specified in the constructor).
   *
   * User would need to dynamic_cast the returned 
   * 'const vmm_ralf_blk_or_sys_typ *' pointer to 
   * 'const vmm_ralf_blk_typ *' or 'const vmm_ralf_sys_typ *' to find out if 
   * the RALF top is a block or a system, and then, get aceess to the rest
   * of the block/system data using that dynamic_cast-ed pointer.
   *
   * @return Pointer to const RALF block or system descriptor.
   */
   const vmm_ralf_blk_or_sys_typ * getTopLevelBlockOrSys() const;


private:
  /**
   * Disabling Copy/Assign Operations.
   */
   RALF_DISABLE_COPY_AND_ASSIGN(vmm_ralf)

   std::string rtl_dir_;
   vmm_ralf_blk_or_sys_typ * ralf_data_;
};

} // end: namespace 'ralf'

#endif

