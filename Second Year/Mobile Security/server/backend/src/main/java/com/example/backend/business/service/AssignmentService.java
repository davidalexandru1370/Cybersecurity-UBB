package com.example.backend.business.service;

import java.util.Date;
import java.util.List;
import java.util.Optional;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import com.example.backend.business.entities.AssignmentDTO;
import com.example.backend.business.entities.CreateAssignmentDTO;
import com.example.backend.business.entities.UpdateAssignmentDTO;
import com.example.backend.business.repository.AssigneesRepository;
import com.example.backend.business.repository.AssignmentRepository;
import com.example.backend.business.repository.CourseRepository;
import com.example.backend.business.repository.UserRepository;
import com.example.backend.business.service.interfaces.IAssignmentService;
import com.example.backend.core.domain.Assignees;
import com.example.backend.core.domain.Assignment;
import com.example.backend.core.exceptions.NotFoundException;

@Service
public class AssignmentService implements IAssignmentService {
    @Autowired
    private AssignmentRepository assignmentRepository;

    @Autowired
    private AssigneesRepository assigneesRepository;

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
        for (var studentId : createAssignmentDTO.getStudents()) {
            var student = userRepository.findById(studentId)
                    .orElseThrow(() -> new NotFoundException("Student not found"));
            var assignee = new Assignees(assignment, student);
            assigneesRepository.save(assignee);
        }

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
    public AssignmentDTO getAssignmentById(Long assignmentId) throws NotFoundException {
        Assignment assignment = assignmentRepository.findById(assignmentId)
                .orElseThrow(() -> new NotFoundException("Assignment not found"));

        return new AssignmentDTO(assignmentId, assignment.getTitle(), assignment.getDescription(),
                assignment.getCourse().getId(), Optional.ofNullable(assignment.getDueDate()));
    }

    @Override
    public List<AssignmentDTO> getStudentAssignments(Long studentId) {
        var assignees = assigneesRepository.findByUser_Id(studentId);

        var assignments = assignees.stream()
                .map(a -> {
                    var assignment = a.getAssignment();
                    return new AssignmentDTO(
                            assignment.getId(),
                            assignment.getTitle(),
                            assignment.getDescription(),
                            assignment.getCourse().getId(),
                            Optional.ofNullable(assignment.getDueDate()));
                })
                .toList();
        return assignments;
    }

    @Override
    public List<AssignmentDTO> getTeacherAssignments(Long teacherId) throws NotFoundException {
        var assignments = assignmentRepository.findByTeacher_Id(teacherId).stream()
                .map(assignment -> {

                    return new AssignmentDTO(
                            assignment.getId(),
                            assignment.getTitle(),
                            assignment.getDescription(),
                            assignment.getCourse().getId(),
                            Optional.ofNullable(assignment.getDueDate()));
                })
                .toList();

        return assignments;
    }
}
