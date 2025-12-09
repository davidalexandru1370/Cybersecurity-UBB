package com.example.backend.business.entities;

public class SubmitAssignmentDTO {
    private Long studentId;
    private Long assignmentId;
    private String content;

    public SubmitAssignmentDTO(Long studentId, Long assignmentId, String content) {
        this.studentId = studentId;
        this.assignmentId = assignmentId;
        this.content = content;
    }

    public Long getStudentId() {
        return studentId;
    }

    public Long getAssignmentId() {
        return assignmentId;
    }

    public String getContent() {
        return content;
    }
}
