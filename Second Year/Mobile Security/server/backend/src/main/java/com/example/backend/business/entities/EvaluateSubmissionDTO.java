package com.example.backend.business.entities;

public class EvaluateSubmissionDTO {
    private Long teacherId;
    private Long submissionId;
    private Float grade;
    private String feedback;

    public EvaluateSubmissionDTO(Long teacherId, Long submissionId, Float grade, String feedback) {
        this.teacherId = teacherId;
        this.submissionId = submissionId;
        this.grade = grade;
        this.feedback = feedback;
    }

    public Float getGrade() {
        return grade;
    }

    public String getFeedback() {
        return feedback;
    }

    public Long getSubmissionId() {
        return submissionId;
    }

    public Long getTeacherId() {
        return teacherId;
    }
}
