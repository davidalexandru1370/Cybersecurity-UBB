package com.example.backend.business.service;

import java.util.Date;
import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import com.example.backend.business.entities.AssignmentDTO;
import com.example.backend.business.entities.CreateAssignmentDTO;
import com.example.backend.business.entities.UpdateAssignmentDTO;
import com.example.backend.business.repository.AssignmentRepository;
import com.example.backend.business.repository.CourseRepository;
import com.example.backend.business.repository.UserRepository;
import com.example.backend.business.service.interfaces.IAssignmentService;
import com.example.backend.core.domain.Assignment;
import com.example.backend.core.exceptions.NotFoundException;

@Service
public class AssignmentService implements IAssignmentService {
    @Autowired
    private AssignmentRepository assignmentRepository;

    @Autowired
    private UserRepository userRepository;

    @Autowired
    private CourseRepository courseRepository;

    @Override
    public Long createAssignment(Long teacherId, CreateAssignmentDTO createAssignmentDTO)
            throws NotFoundException {
        var teacher = userRepository.findById(teacherId).orElseThrow(() -> new NotFoundException("Teacher not found"));
        var course = courseRepository.findById(createAssignmentDTO.getCourseId())
                .orElseThrow(() -> new NotFoundException("Course not found"));
        Date dueDate = null;

        if (createAssignmentDTO.getDueDate() != null && createAssignmentDTO.getDueDate().isPresent()) {
            dueDate = new Date(createAssignmentDTO.getDueDate().get() * 1000);
        }

        var assignment = new Assignment(createAssignmentDTO.getTitle(), createAssignmentDTO.getDescription(),
                dueDate, course, teacher);

        assignment = assignmentRepository.save(assignment);

        return assignment.getId();
    }

    @Override
    public void deleteAssignment(Long assignmentId) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'deleteAssignment'");
    }

    @Override
    public void updateAssignment(Long assignmentId, UpdateAssignmentDTO updateAssignmentDTO) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'updateAssignment'");
    }

    @Override
    public AssignmentDTO getAssignmentById(Long assignmentId) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'getAssignmentById'");
    }

    @Override
    public List<AssignmentDTO> getStudentAssignments(Long studentId) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'getStudentAssignments'");
    }

}
