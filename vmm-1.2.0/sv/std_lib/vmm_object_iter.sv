/*********************************************************************
 *    Copyright 2004-2009 Synopsys, Inc.
 *    All Rights Reserved Worldwide
 *
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

/**                          
This iterator uses the Breadth First Search (BFS) algorithm. For the hierarchical
tree shown below the order in which the iterator will traverse through the given 
tree is A, B, A:X, A:Y, B:X & B:Y

                                  Root
                          _________|_________ 
                         |                   |
                         A                   B
                      ___|___             ___|___ 
                     |       |           |       |
                     X       Y           X       Y

*/

// Macro to iterate over all objects of a specified type and name under a specified root
`define foreach_vmm_object(classtype, name, root) \
   classtype obj; \
   vmm_object_iter obj_iter = new(root, name); \
   for (vmm_object _obj = obj_iter.first(); \
        _obj != null; \
        _obj = obj_iter.next()) \
     if ($cast(obj, _obj))

`define foreach_vmm_object_in_namespace(classtype, name, space, root) \
   classtype obj; \
   vmm_object_iter obj_iter = new(root, name, space); \
   for (vmm_object _obj = obj_iter.first(); \
        _obj != null; \
        _obj = obj_iter.next()) \
     if ($cast(obj, _obj))

/**
 Constructor of the iterator class
*/
function vmm_object_iter::new( vmm_object root,
                               string  name,
                               string space
                             );

   this.name = name;
   this._space = space;

   if (root == null) begin
     /**
      Set the _null_root flag to 1;
     */
     _null_root = 1;
   end
   else begin
     _root = root;
   end

  /**
   Transforming the match pattern into a regular expression. The method is 
   available within the vmm_object class.
   */
  _regex = vmm_path_match::compile_pattern(name, log);

   void'(this.first());
   
endfunction: new

function vmm_object vmm_object_iter::first();

  vmm_log log;
  vmm_object root, iter, obj;
  int nth_root = 0;
  
  //string str;
  `vmm_path_compiled compiled_path;

  /**
   Delete the queues before starting
   */
  _bfs_obj_q.delete();
  _root_q.delete();

  if (_null_root) begin
    /**
     Store all the roots if a null root is specified
    */
    iter = vmm_object::get_nth_root(nth_root, _space);

    while(iter!=null) begin
      _root_q.push_back(iter);
      nth_root++;
      iter = vmm_object::get_nth_root(nth_root, _space);
    end
  end
  else begin
    iter = _root;
    if(iter.is_in_namespace(_space))
      _root_q.push_back(iter);
    else
      `vmm_error(this.log,`vmm_sformatf("the root specified does not belong to the namespace %s specified", _space));
  end

  /**
   Below this is the recursive logic that queues up the tree using Breadth First
   Search(BFS) algorithm. Look at the top of this file for information on the 
   algorithm.
   */
  _root = _root_q.pop_front();
  root  = _root;

  while(root!=null) begin
    /**
     Insert all the children into our search queue.
     */
    if(root.get_num_children() > 0)
    for(int i=0; i < root.get_num_children(); i++) begin
       obj = root.get_nth_child(i);
        _bfs_obj_q.push_back(obj);
    end

    /**
     Pop the objects from the BSF queue
     */
    iter = _bfs_obj_q.pop_front();
    while(iter!=null) begin
      compiled_path = vmm_path_match::compile_path(log, iter, );

      for(int i=0; i < iter.get_num_children(); i++) begin
        obj = iter.get_nth_child(i);
        _bfs_obj_q.push_back(obj);
      end
      
      if(vmm_path_match::match(compiled_path, _regex)) return iter;

      /**
       Pop the next object from the BSF queue
       */
      iter = _bfs_obj_q.pop_front();
    end
    /**
     Pop the next root from the root queue
     */
    _root = _root_q.pop_front();
    root = _root;
  end
  
  return null;

endfunction : first

function vmm_object vmm_object_iter::next();

  /**
   Local container to capture the logs
   */
  vmm_log log;

  vmm_object root, iter, obj;
  `vmm_path_compiled compiled_path; 

  /**
   Use the root which was used last by first()
   */
  root = _root;

  while(root!=null) begin
    /**
      A similar logic like the one used in the method first()
     */
    iter = _bfs_obj_q.pop_front();
    
    while(iter!=null) begin
      compiled_path = vmm_path_match::compile_path(log, iter, );
    
      for(int i=0; i < iter.get_num_children(); i++) begin
        obj = iter.get_nth_child(i);
        _bfs_obj_q.push_back(obj);
      end
 
      if(vmm_path_match::match(compiled_path, _regex)) return iter;

      iter = _bfs_obj_q.pop_front();
    end
    _root = _root_q.pop_front();
    root = _root;
    
    if(root!=null)
      for(int i=0; i < root.get_num_children(); i++) begin
          obj = root.get_nth_child(i); 
          _bfs_obj_q.push_back(obj);
      end
  end
  return null;

endfunction : next
