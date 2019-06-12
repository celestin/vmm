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

// Class: vmm_object_iter
//
//
// This is the <vmm_object> hierarchy traversal iterator class.
//
// The <vmm_object_iter> class traverses the hierarchy rooted at the specified object, 
// looking for objects whose relative hierarchical name matches the specified name. 
// Beginning at a specific object, you can traverse through the hierarchy through 
// the different methods like the <first> and <next> methods.
  
// //////////////////////////////////////////// 
// Function: new 
// 
// Traverses the hierarchy rooted at the specified root object, looking for objects whose
// relative hierarchical name in the specified namespace matches the specified name.
// The object name is relative to the specified root object. If no object is specified,
// traverses all hierarchies and the hierarchical name is absolute. The specified root
// (if any) is not included in the iteration. 
// 
//|   / Match pattern - /a1/, with root object e11 vmm_object_iter  
//|      iter = new ("/a1/", e11 ); 
// 

function vmm_object_iter::new( vmm_object root = null,
                               string  name = "",
                               string space = ""
                             );

   this.name = name;
   this._space = space;

   if (root == null) begin
     // Set the _null_root flag to 1;
     _null_root = 1;
   end
   else begin
     _root = root;
   end

   // Transforming the match pattern into a regular expression. The method is 
   // available within the vmm_object class.
  _regex = vmm_path_match::compile_pattern(name, log);

   void'(this.first());
   
endfunction: new

// //////////////////////////////////////////// 
// Function: first 
// 
// Resets the state of the iterator to the first object in the vmm_object hierarchy. Returns
// null, if the specified hierarchy contains no child objects. 
// 
//|   class E extends vmm_object;
//|      ...
//|   endclass 
//|   ...
//|   initial begin
//|      E e11 = new ("e1");
//|      vmm_object obj;
//|      vmm_object_iter  iter = new("/a1/", e11 ); 
//|      ...
//|      obj = iter.first();
//|      ...
//|   end
function vmm_object vmm_object_iter::first();
  vmm_log log;
  vmm_object root, iter, obj;
  int nth_root = 0;
  
  `vmm_path_compiled compiled_path;

   // Delete the queues before starting
  _bfs_obj_q.delete();
  _root_q.delete();

  if (_null_root) begin
    // Store all the roots if a null root is specified
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

  // Recursive logic that queues up the tree using Breadth First
  // Search(BFS) algorithm. Look at the top of this file for information on the 
  // algorithm.
  _root = _root_q.pop_front();
  root  = _root;

  while(root!=null) begin
    // Insert all the children into our search queue.
    if(root.get_num_children() > 0)
    for(int i=0; i < root.get_num_children(); i++) begin
       obj = root.get_nth_child(i);
        _bfs_obj_q.push_back(obj);
    end

    // Pop the objects from the BSF queue
    iter = _bfs_obj_q.pop_front();
    while(iter!=null) begin
      compiled_path = vmm_path_match::compile_path(log, iter, );

      for(int i=0; i < iter.get_num_children(); i++) begin
        obj = iter.get_nth_child(i);
        _bfs_obj_q.push_back(obj);
      end
      
      if(vmm_path_match::match(compiled_path, _regex)) return iter;

      // Pop the next object from the BSF queue
      iter = _bfs_obj_q.pop_front();
    end
    // Pop the next root from the root queue
    _root = _root_q.pop_front();
    root = _root;
  end
  
  return null;
endfunction : first

// Function: next 
// Returns the next object in the vmm_object hierarchy. Returns null, if there are no more 
// child objects. Objects are traversed depth first.
//
//|    vmm_object obj;
//|    vmm_object_iter iter = new(e11, "/a1/");
//|    ...
//|    obj = iter.first();
//|    while (obj != null)
//|      begin
//|        ...
//|        obj = iter.next;
//|      end
//|    ...
  
function vmm_object vmm_object_iter::next();
  // Local container to capture the logs
  vmm_log log;

  vmm_object root, iter, obj;
  `vmm_path_compiled compiled_path; 

  // Use the root which was used last by first()
  root = _root;

  while(root!=null) begin
    // A similar logic like the one used in the method first()
    if (_bfs_obj_q.size() == 0)
       iter = null;
    else
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
    if (_root_q.size() == 0)
       _root = null;
    else 
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
